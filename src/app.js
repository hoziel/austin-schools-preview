// Austin Schools Explorer. Data is loaded from /data. The map is MapLibre; overlays are drawn on a canvas above it.
// The page asks for this file as app.js?v=<version>. The same version goes on the data files, so a browser never mixes
// a new page with an old cached script, stylesheet or data file.
const VER=new URL(import.meta.url).search;
const load=p=>fetch(p.startsWith("data/")?p+VER:p).then(r=>{if(!r.ok)throw new Error(p+": "+r.status);return r.json()});
const POSITRON="https://tiles.openfreemap.org/styles/positron";
const [SJ,NBGEO,ZGEO,BASEMAP,STREET,PJ]=await Promise.all(
  [...["data/schools.json","data/neighborhoods.geojson","data/school_zones.geojson","data/basemap_v1.json"].map(load),load(POSITRON).catch(()=>null),load("data/private_schools.json").catch(()=>({schools:[]}))]);
// SJ.schools: public campuses with state ID and rating, built by scripts/fetch_schools.mjs.
// PJ.schools: private schools from the federal private school survey, built by scripts/fetch_private_schools.mjs. No state rating;
// `serves` lists the levels a school covers (for example "EM" for K-8).
// Each becomes an array [name, level E/M/H/K, type pub/chr/pvt, district, lat, lng] (the v1 shape) that also carries the named fields.
const PVTC="#7c5cff"; // private schools: no rating colour, so they get their own
const SCHOOLS=[...SJ.schools,...PJ.schools].map(o=>Object.assign([o.name,o.level,o.type,o.district,o.lat,o.lng],o));
const RANK={A:5,B:4,C:3,D:2,F:1};
// NBGEO: neighborhood polygons, built by scripts/fetch_neighborhoods.mjs
// ZGEO: public school attendance zones, built by scripts/fetch_school_zones.mjs
// ROADS, water: hand-approximated lines from v1. Only the offline drive-time model uses them now.
// ROADS: {n, c: hwy/art, r: rush multiplier, p: [[lat,lng],...]}
const {roads:ROADS,water_lines:WATER_LINES,lake_travis:LAKE_TRAVIS}=BASEMAP;

// ---------- GEOMETRY ----------
const LAT0=30.08, LAT1=30.66, LNG0=-98.12, LNG1=-97.48, DLAT=0.005, DLNG=0.0058;
const ROWS=Math.ceil((LAT1-LAT0)/DLAT), COLS=Math.ceil((LNG1-LNG0)/DLNG), N=ROWS*COLS;
const KX=111.32*Math.cos(30.35*Math.PI/180), KY=110.57;
function segDist(px,py,ax,ay,bx,by){const dx=bx-ax,dy=by-ay;const L=dx*dx+dy*dy;let t=L?((px-ax)*dx+(py-ay)*dy)/L:0;t=Math.max(0,Math.min(1,t));const x=ax+t*dx-px,y=ay+t*dy-py;return Math.hypot(x,y)}
function polyDistKm(lat,lng,pts){let m=1e9;const px=lng*KX,py=lat*KY;for(let i=0;i<pts.length-1;i++){m=Math.min(m,segDist(px,py,pts[i][1]*KX,pts[i][0]*KY,pts[i+1][1]*KX,pts[i+1][0]*KY))}return m}
function inPoly(lat,lng,poly){let ins=false;for(let i=0,j=poly.length-1;i<poly.length;j=i++){const yi=poly[i][0],xi=poly[i][1],yj=poly[j][0],xj=poly[j][1];if(((yi>lat)!=(yj>lat))&&(lng<(xj-xi)*(lat-yi)/(yj-yi)+xi))ins=!ins}return ins}
const cellLat=r=>LAT0+(r+0.5)*DLAT, cellLng=c=>LNG0+(c+0.5)*DLNG;
function idxOf(lat,lng){const r=Math.floor((lat-LAT0)/DLAT),c=Math.floor((lng-LNG0)/DLNG);if(r<0||c<0||r>=ROWS||c>=COLS)return -1;return r*COLS+c}

// cell classification
const cls=new Uint8Array(N); // 0 local,1 art,2 hwy,3 blocked
const rushF=new Float32Array(N);
(function classify(){
  for(let r=0;r<ROWS;r++)for(let c=0;c<COLS;c++){
    const i=r*COLS+c,lat=cellLat(r),lng=cellLng(c);
    let k=0,rf=0.8;
    for(const rd of ROADS){const d=polyDistKm(lat,lng,rd.p);
      if(rd.c==="hwy"&&d<0.42){if(k<2||rd.r<rf){k=2;rf=rd.r}}
      else if(rd.c==="art"&&d<0.36&&k<2){k=1;rf=rd.r}}
    if(k<2){ if(inPoly(lat,lng,LAKE_TRAVIS))k=3;
      else for(const w of WATER_LINES){if(w.block&&polyDistKm(lat,lng,w.p)<0.38){k=(k===1&&rf<=0.6)?1:3}} }
    cls[i]=k;rushF[i]=k===0?0.82:rf;
  }
})();
const BASE=[30,52,95,0]; // km/h
let speed=new Float32Array(N);
function setSpeeds(mode){for(let i=0;i<N;i++){const b=BASE[cls[i]];speed[i]=mode==="rush"?b*rushF[i]:b}}

// Dijkstra
const DY=DLAT*KY, DX=DLNG*KX, DD=Math.hypot(DX,DY);
const NB=[[1,0,DY],[-1,0,DY],[0,1,DX],[0,-1,DX],[1,1,DD],[1,-1,DD],[-1,1,DD],[-1,-1,DD]];
function dijkstra(src){ // src: one grid cell, or a list of cells (then each cell gets the time to the nearest of them)
  const t=new Float64Array(N).fill(Infinity);const srcs=(Array.isArray(src)?src:[src]).filter(i=>i>=0); if(!srcs.length)return t;
  const hk=[],hv=[]; // binary heap
  const push=(k,v)=>{hk.push(k);hv.push(v);let i=hk.length-1;while(i>0){const p=(i-1)>>1;if(hv[p]<=hv[i])break;[hk[p],hk[i]]=[hk[i],hk[p]];[hv[p],hv[i]]=[hv[i],hv[p]];i=p}};
  const pop=()=>{const k=hk[0],v=hv[0];const lk=hk.pop(),lv=hv.pop();if(hk.length){hk[0]=lk;hv[0]=lv;let i=0;for(;;){let l=2*i+1,r=l+1,m=i;if(l<hk.length&&hv[l]<hv[m])m=l;if(r<hk.length&&hv[r]<hv[m])m=r;if(m===i)break;[hk[m],hk[i]]=[hk[i],hk[m]];[hv[m],hv[i]]=[hv[i],hv[m]];i=m}}return [k,v]};
  for(const i of srcs){t[i]=0;push(i,0)}
  while(hk.length){const [u,tu]=pop();if(tu>t[u])continue;if(tu>90)break;
    const r=(u/COLS)|0,c=u-r*COLS,su=speed[u]||8;
    for(const [dr,dc,d] of NB){const rr=r+dr,cc=c+dc;if(rr<0||cc<0||rr>=ROWS||cc>=COLS)continue;const v=rr*COLS+cc;const sv=speed[v];if(!sv)continue;
      const nt=tu+d/((su+sv)/2)*60;if(nt<t[v]){t[v]=nt;push(v,nt)}}}
  return t;
}
const ACCESS=2; // minutes to get to/from the road network
function timeAt(grid,lat,lng){const i=idxOf(lat,lng);if(i<0)return Infinity;if(isFinite(grid[i]))return grid[i]+ACCESS;const r=(i/COLS)|0,c=i-r*COLS;let m=Infinity;for(let dr=-1;dr<=1;dr++)for(let dc=-1;dc<=1;dc++){const rr=r+dr,cc=c+dc;if(rr>=0&&cc>=0&&rr<ROWS&&cc<COLS)m=Math.min(m,grid[rr*COLS+cc])}return m+ACCESS+1}

// ---------- STATE ----------
const S={mode:"free",sm:8,minR:5,size:new Set([1,2,3]),levels:new Set(["E","M","H","K"]),types:new Set(["pub","chr","pvt"]),
  sel:null,home:null,placingHome:false,tab:"sc",base:"sat",lvl:"M",lyIso:false,lyNm:true,lyNb:true,lyZip:true,lyRd:false,lyZ:{E:false,M:true,H:false}};
// Map style. Default: neighborhoods as names only, school zones filled with their school's state rating colour,
// school markers coloured by rating with the shape telling the level. Other styles from the address bar:
//   ?nb=names|outline &zf=rating|none &dc=rating|level &z=EMH (zone levels on) &base=map|sat &zip=0
const Q=new URLSearchParams(location.search);
S.nb=Q.get("nb")||"names";S.zf=Q.get("zf")||"rating";S.dc=Q.get("dc")||"rating";
if(Q.get("base"))S.base=Q.get("base");if(Q.has("r"))S.minR=+Q.get("r");
if(Q.has("full"))document.querySelector(".app").classList.add("full"); // map only, for screenshots
if(Q.get("zip")==="0")S.lyZip=false;
if(Q.has("z"))for(const L of "EMH")S.lyZ[L]=Q.get("z").includes(L);
const RC={A:"#1a9850",B:"#7fbf3f",C:"#e6b800",D:"#ef7d1a",F:"#d73027"};
// NBpoly[k]: outer rings of neighborhood k as [[lat,lng],...]. Holes are ignored.
const NBpoly=NBGEO.features.map(f=>f.geometry.coordinates.map(p=>p[0].map(([x,y])=>[y,x])));
// NBHDS keeps the v1 row shape: [name, lat, lng, half-width km, half-height km]. lat/lng is a point inside the polygon.
const NBHDS=NBGEO.features.map((f,k)=>{const pts=NBpoly[k].flat(),la=pts.map(p=>p[0]),ln=pts.map(p=>p[1]);const [clng,clat]=f.properties.center;
  return [f.properties.name,clat,clng,(Math.max(...ln)-Math.min(...ln))*KX/2,(Math.max(...la)-Math.min(...la))*KY/2]});

// Tier: "focus" (the six), "area" (other published neighborhoods) or "zip" (ZIP code areas, which leave no gaps).
const NBTIER=NBGEO.features.map(f=>f.properties.tier),NBAREA=NBGEO.features.map(f=>f.properties.area_sqkm);
const nbShown=k=>NBTIER[k]==="zip"?S.lyZip:S.lyNb;

// ---------- SCHOOL ZONES ----------
// polys: [[outer ring, ...holes], ...] as [lat,lng]. bb: [lat0,lng0,lat1,lng1].
const ZONES=ZGEO.features.map(f=>{const polys=f.geometry.coordinates.map(p=>p.map(r=>r.map(([x,y])=>[y,x])));
  const pts=polys.flatMap(p=>p[0]),la=pts.map(p=>p[0]),ln=pts.map(p=>p[1]);
  return {...f.properties,polys,bb:[Math.min(...la),Math.min(...ln),Math.max(...la),Math.max(...ln)],
    short:f.properties.school.replace(/ (Elementary|Middle|High)( School)?$/,""),
    sch:SCHOOLS.find(s=>s.zone===f.properties.school&&s.level===f.properties.level&&s.district===f.properties.district)||null}});
const inZone=(z,lat,lng)=>lat>=z.bb[0]&&lat<=z.bb[2]&&lng>=z.bb[1]&&lng<=z.bb[3]&&z.polys.some(p=>inPoly(lat,lng,p[0])&&!p.slice(1).some(h=>inPoly(lat,lng,h)));
// The zone a point falls in, per level (null when no zone data covers it)
const zonedAt=(lat,lng)=>Object.fromEntries(["E","M","H"].map(L=>[L,ZONES.find(z=>z.level===L&&inZone(z,lat,lng))||null]));


// Home pin: kept in this browser only (localStorage), never in a file. homeGrid holds the drive from it to every cell.
try{const h=JSON.parse(localStorage.getItem("home"));if(h&&isFinite(h.lat)&&isFinite(h.lng))S.home=h}catch(e){}
let homeGrid=null;
function computeHome(){setSpeeds(S.mode);const i=S.home?idxOf(S.home.lat,S.home.lng):-1;homeGrid=i>=0?dijkstra(i):null}
const homeT=s=>homeGrid?timeAt(homeGrid,s[4],s[5]):null;
function setHome(h){S.home=h;S.placingHome=false;try{h?localStorage.setItem("home",JSON.stringify(h)):localStorage.removeItem("home")}catch(e){}computeHome();updPlaceUI();renderAll()}
function recompute(){
  setSpeeds(S.mode);computeHome();
}
// School size ranges for the size pill: [label, from, below]. Any number can be ticked; none ticked means any size.
// A school with no student count passes only when none is ticked.
const SIZES=[["Under 300",0,300],["300–600",300,600],["600–1,000",600,1000],["Over 1,000",1000,Infinity]];
const sizeOK=s=>!S.size.size||[...S.size].some(i=>s.students>=SIZES[i][1]&&s.students<SIZES[i][2]);
// The letter a school is rated by: the state rating for public schools; for private schools, which the state does not rate,
// the Niche grade without its plus or minus (null when Niche has not graded the school).
const rate=s=>s[2]==="pvt"?(s.niche?s.niche[0]:null):s.tea;
// A private school with no grade always passes the minimum rating, since there is nothing to judge it by.
const passFilter=s=>(s.serves?[...s.serves].some(L=>S.levels.has(L)):S.levels.has(s[1]))&&S.types.has(s[2])&&((s[2]==="pvt"&&!s.niche)||(RANK[rate(s)]||0)>=S.minR)&&sizeOK(s);

// ---------- RENDER ----------
const cv=document.getElementById("cv"),ctx=cv.getContext("2d"),main=document.getElementById("mapwrap");
const MOBILE=matchMedia("(max-width:900px)"),COARSE=matchMedia("(pointer:coarse)");
// Basemaps. Street: OpenFreeMap Positron. Satellite: Esri World Imagery with Positron's place and road names on top.
const SAT_SRC={type:"raster",tiles:["https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}"],tileSize:256,maxzoom:19,attribution:"Imagery © Esri, Maxar, Earthstar Geographics"};
function baseStyle(b){if(b!=="sat")return STREET||POSITRON;
  const st=STREET?structuredClone(STREET):{version:8,sources:{},layers:[]};st.sources.sat=SAT_SRC;
  st.layers=[{id:"sat",type:"raster",source:"sat"},...st.layers.filter(l=>l.type==="symbol").map(l=>({...l,paint:{...l.paint,"text-color":"#fff","text-halo-color":"rgba(0,0,0,.8)","text-halo-width":1.3}}))];return st}
const map=new maplibregl.Map({container:"map",style:baseStyle(S.base),center:[-97.80,30.34],zoom:10.5,
  dragRotate:false,pitchWithRotate:false,touchPitch:false,attributionControl:{compact:true}});
if(Q.has("full"))window._map=map;
map.touchZoomRotate.disableRotation();map.keyboard.disableRotation();
const FOCUS=[[-97.94,30.265],[-97.72,30.40]]; // the six focus neighborhoods
let W=0,H=0,DPR=1;const V={z:16}; // V.z = screen px per km, refreshed on every draw
function resize(){DPR=window.devicePixelRatio||1;W=main.clientWidth;H=main.clientHeight;cv.width=W*DPR;cv.height=H*DPR;draw()}
function fit(){map.fitBounds(FOCUS,{padding:MOBILE.matches?{top:100,bottom:90,left:12,right:12}:24,duration:0})}
// The map is never rotated, so screen x depends only on lng and y only on lat.
let CEN={lng:-97.80,lat:30.34};
const X=lng=>map.project([lng,CEN.lat]).x, Y=lat=>map.project([CEN.lng,lat]).y;
const toLL=(x,y)=>{const p=map.unproject([x,y]);return {lng:p.lng,lat:p.lat}};
const isoCv=document.createElement("canvas");isoCv.width=COLS;isoCv.height=ROWS;
const STOPS=[[0,[26,152,80]],[10,[145,207,96]],[20,[217,239,139]],[30,[254,224,139]],[40,[252,141,89]],[50,[215,48,39]],[60,[165,0,38]]];
function colorFor(t){for(let i=1;i<STOPS.length;i++){if(t<=STOPS[i][0]){const [t0,c0]=STOPS[i-1],[t1,c1]=STOPS[i];const f=(t-t0)/(t1-t0);return c0.map((v,k)=>Math.round(v+(c1[k]-v)*f))}}return STOPS[STOPS.length-1][1]}
// Drive-time shading: minutes to the nearest school that passes the filters.
// Colours run from 0 to the "drive to school" limit; past the "drive to school" limit the map is dimmed instead. Rebuilt only when its inputs change.
let isoGrid=null,isoKey="";
function ensureIso(){
  const key=[S.mode,[...S.levels],[...S.types],S.minR,[...S.size],S.sm].join("|");if(key===isoKey)return;isoKey=key;setSpeeds(S.mode);
  isoGrid=dijkstra(SCHOOLS.filter(passFilter).map(s=>idxOf(s[4],s[5])));
  const g=isoCv.getContext("2d"),img=g.createImageData(COLS,ROWS);
  if(isoGrid)for(let r=0;r<ROWS;r++)for(let c=0;c<COLS;c++){if(cls[r*COLS+c]===3)continue;const t=isoGrid[r*COLS+c]+ACCESS;const o=((ROWS-1-r)*COLS+c)*4;
    if(t<=S.sm){const col=colorFor(t/S.sm*60);img.data[o]=col[0];img.data[o+1]=col[1];img.data[o+2]=col[2];img.data[o+3]=125}
    else{img.data[o]=15;img.data[o+1]=15;img.data[o+2]=25;img.data[o+3]=95}}
  g.putImageData(img,0,0);document.getElementById("lgmax").textContent=S.sm+" min";
}
const NAME_MAX=16,NAME_ZOOM=38; // school name labels: longest label in characters, and the zoom (screen px per km) from which they show
const shortName=n=>{n=n.replace(/ (Elementary|Middle|High|Junior High)( School)?$/,"").replace(/^The /,"");return n.length>NAME_MAX?n.slice(0,NAME_MAX-1).trimEnd()+"…":n};
function path(pts){ctx.beginPath();pts.forEach((p,i)=>{const x=X(p[1]),y=Y(p[0]);i?ctx.lineTo(x,y):ctx.moveTo(x,y)})}
function shape(ctx,x,y,r,type){ctx.beginPath();if(type==="pvt"){ctx.rect(x-r*.9,y-r*.9,r*1.8,r*1.8)}else if(type==="chr"){ctx.moveTo(x,y-r*1.25);ctx.lineTo(x+r*1.25,y);ctx.lineTo(x,y+r*1.25);ctx.lineTo(x-r*1.25,y);ctx.closePath()}else ctx.arc(x,y,r,0,Math.PI*2)}
const LVLC={E:"#0f9d8a",M:"#d98a00",H:"#4f46e5",K:"#a21caf"}; // on white panels and the street map
const LVLC_SAT={E:"#3ef0d0",M:"#ffb733",H:"#b9b0ff",K:"#f3a0ff"}; // brighter, to read on satellite imagery
const ZDASH={E:[],M:[8,5],H:[1,6]},ZW={E:1.8,M:2.2,H:3}; // the map key in style.css draws the same strokes
function draw(){
  if(!W)return;ensureIso();CEN=map.getCenter();V.z=Math.abs(Y(CEN.lat+1/KY)-Y(CEN.lat));
  const sat=S.base==="sat",MC=sat?LVLC_SAT:LVLC,NBC=sat?"#ffe04a":"#1d2433",CASE=sat?"rgba(0,0,0,.6)":"rgba(255,255,255,.85)",LINK=sat?"rgba(255,255,255,.8)":"rgba(47,91,211,.55)",ZIPC=sat?"#ffffff":"#6b7385";
  // every boundary is a coloured line on a contrasting casing, so it reads on imagery and on the street map
  const cased=(w,col)=>{ctx.lineWidth=w+2.4;ctx.strokeStyle=CASE;ctx.stroke();ctx.lineWidth=w;ctx.strokeStyle=col;ctx.stroke()};
  const label=(t,x,y,col)=>{ctx.lineWidth=3.5;ctx.strokeStyle=sat?"rgba(0,0,0,.85)":"rgba(255,255,255,.9)";ctx.strokeText(t,x,y);ctx.fillStyle=col;ctx.fillText(t,x,y)};
  ctx.setTransform(DPR,0,0,DPR,0,0);ctx.clearRect(0,0,W,H);ctx.lineCap="round";ctx.lineJoin="round";
  // iso
  if(S.lyIso&&isoGrid){const x0=X(LNG0),y0=Y(LAT0+ROWS*DLAT);ctx.imageSmoothingEnabled=true;ctx.drawImage(isoCv,x0,y0,X(LNG0+COLS*DLNG)-x0,Y(LAT0)-y0)}
  // school zones
  const selS=S.sel&&S.sel.t==="sc"?SCHOOLS[S.sel.i]:null;
  const fillL=S.zf==="rating"&&!(S.lyIso&&isoGrid)?["E","M","H"].find(L=>S.lyZ[L]):null; // rating fill for the youngest level shown, so fills never stack
  const pubOn=S.types.has("pub")||S.types.has("chr"); // attendance zones belong to public schools, so they go when only private schools are shown
  for(const L of ["H","M","E"]){if(!S.lyZ[L]||!pubOn)continue;ctx.setLineDash(ZDASH[L]);
    for(const z of ZONES){if(z.level!==L)continue;ctx.beginPath();
      for(const p of z.polys)for(const r of p){r.forEach((q,i)=>{const x=X(q[1]),y=Y(q[0]);i?ctx.lineTo(x,y):ctx.moveTo(x,y)});ctx.closePath()}
      if(L===fillL){ctx.globalAlpha=sat?.42:.34;ctx.fillStyle=RC[z.sch&&z.sch.tea]||"#9aa0aa";ctx.fill("evenodd");ctx.globalAlpha=1}
      cased(ZW[L],MC[L])}}
  ctx.setLineDash([]);
  // neighborhoods
  // ZIP areas first (thin, long dashes, no fill), then other neighborhoods, then the six focus areas on top
  for(const T of ["zip","area","focus"])NBpoly.forEach((rings,k)=>{if(NBTIER[k]!==T||!nbShown(k))return;const sel=false;if(S.nb==="names")return;ctx.beginPath();
      for(const r of rings){r.forEach((p,i)=>{const x=X(p[1]),y=Y(p[0]);i?ctx.lineTo(x,y):ctx.moveTo(x,y)});ctx.closePath()}
      const a=sel?.24:T==="focus"?.08:T==="area"?.04:0;if(a){ctx.fillStyle=sat?`rgba(255,224,74,${a})`:`rgba(29,36,51,${a*.7})`;ctx.fill()}
      ctx.setLineDash(T==="zip"?[14,7]:[]);cased(sel?3.6:T==="focus"?2.4:T==="area"?1.5:1.1,T==="zip"?ZIPC:NBC);ctx.setLineDash([])});
  // roads
  if(S.lyRd){for(const rd of ROADS){path(rd.p);ctx.strokeStyle="#fff";ctx.lineWidth=rd.c==="hwy"?5:3;ctx.stroke();ctx.strokeStyle=rd.c==="hwy"?"#9a8f7a":"#c4bba8";ctx.lineWidth=rd.c==="hwy"?2.5:1.3;ctx.stroke()}}
  // links: only from a picked place to the schools within the limit, each labelled with its minutes

  // labels: neighborhoods
  // Focus names always; other neighborhoods once they are wide enough to hold the name; ZIP names when zoomed in a little
  if(V.z>11){ctx.textAlign="center";ctx.textBaseline="middle";
    for(const T of ["zip","area","focus"]){ctx.font=`${T==="focus"?"600 13px":T==="area"?"500 11.5px":"500 11px"} 'IBM Plex Sans',sans-serif`;
      NBHDS.forEach((n,k)=>{if(NBTIER[k]!==T||!nbShown(k))return;const sel=S.sel&&S.sel.t==='nb'&&S.sel.i===k;
        if(!sel&&(T==="focus"?n[3]*V.z<16:T==="area"?n[3]*V.z<ctx.measureText(n[0]).width*(S.nb==="names"?.35:.6):V.z<(S.nb==="names"?11:16)))return;
        const x=X(n[2]),y=Y(n[1])+(T==="zip"?16:0);if(x<-50||x>W+50||y<-20||y>H+20)return;label(n[0],x,y,T==="zip"?ZIPC:NBC)})}}
  // road labels
  if(S.lyRd&&V.z>9){ctx.font="600 10px 'IBM Plex Mono',monospace";ctx.textAlign="center";
    for(const rd of ROADS){if(rd.c!=="hwy")continue;const p=rd.p[Math.floor(rd.p.length/2)];const x=X(p[1]),y=Y(p[0]);const w=ctx.measureText(rd.n).width+8;ctx.fillStyle="#fff";ctx.fillRect(x-w/2,y-7,w,14);ctx.strokeStyle="#9a8f7a";ctx.lineWidth=1;ctx.strokeRect(x-w/2,y-7,w,14);ctx.fillStyle="#5b5446";ctx.fillText(rd.n,x,y+.5)}}
  // schools
  const r=Math.max(4.5,Math.min(9,V.z/3));ctx.font="600 10px 'IBM Plex Mono',monospace";ctx.textAlign="center";ctx.textBaseline="middle";
  SCHOOLS.forEach((s,j)=>{const x=X(s[5]),y=Y(s[4]);const ok=passFilter(s),inC=true;
    const sel=S.sel&&S.sel.t==="sc"&&S.sel.i===j;
    if(!ok){return}
    const byR=S.dc==="rating";
    shape(ctx,x,y,sel?r+2:(inC?r:r*.75),byR?{E:"pub",M:"chr",H:"pvt",K:"pub"}[s[1]]:s[2]);ctx.fillStyle=byR?(s[2]==="pvt"&&!s.niche?PVTC:RC[rate(s)]||"#9aa0aa"):!inC?"#b9b6ae":MC[s[1]];ctx.globalAlpha=selS&&!sel?.4:byR&&!inC?.55:1;ctx.fill();ctx.lineWidth=sel?3:s[2]==="pvt"&&byR?2.6:1.5;ctx.strokeStyle=sel?(sat?"#ffe04a":"#111"):s[2]==="pvt"&&byR?PVTC:(sat?"#111":"#fff");ctx.stroke();ctx.globalAlpha=1; // private schools keep a purple ring; the rest fade while one school is selected
    const lt=s[2]==="pvt"&&!s.niche?"?":rate(s);if(r>=7.5&&lt){ctx.fillStyle=sat&&inC&&!byR?"#111":"#fff";ctx.fillText(lt,x,y+.5)}});
  // school names: small, to the right of the marker, cut to NAME_MAX characters; only once zoomed in enough to fit them
  if(S.lyNm&&V.z>=NAME_ZOOM){ctx.font="500 10.5px 'IBM Plex Sans',sans-serif";ctx.textAlign="left";
    SCHOOLS.forEach(s=>{if(s===selS||!passFilter(s))return;const x=X(s[5]),y=Y(s[4]);if(x<-20||x>W||y<0||y>H)return;label(shortName(s[0]),x+r+5,y+.5,sat?"#fff":"#1d2433")});
    ctx.textAlign="center";ctx.font="600 10px 'IBM Plex Mono',monospace"}
  // school zone labels
  if(V.z>22){ctx.textAlign="center";ctx.textBaseline="middle";
    for(const L of ["H","M","E"]){if(!S.lyZ[L]||!pubOn)continue;ctx.font=`${L==="E"?"500 11px":"600 12px"} 'IBM Plex Sans',sans-serif`;
      for(const z of ZONES){if(z.level!==L)continue;const x=X(z.center[0]),y=Y(z.center[1])+(L==="M"?12:L==="H"?-12:0);if(x<0||x>W||y<0||y>H)continue;label(z.short,x,y,MC[L])}}}
  // selected school: its attendance zone outlined, a line from the home pin with the minutes, a ring and its full name
  if(selS){const x=X(selS[5]),y=Y(selS[4]),hi=sat?"#ffe04a":"#111827";
    const z=ZONES.find(z=>z.sch===selS);
    if(z){ctx.beginPath();for(const p of z.polys)for(const q of p){q.forEach((c,i)=>{const a=X(c[1]),b=Y(c[0]);i?ctx.lineTo(a,b):ctx.moveTo(a,b)});ctx.closePath()}
      ctx.globalAlpha=.18;ctx.fillStyle=hi;ctx.fill("evenodd");ctx.globalAlpha=1;ctx.lineJoin="round";ctx.lineWidth=6;ctx.strokeStyle=sat?"rgba(0,0,0,.6)":"rgba(255,255,255,.8)";ctx.stroke();ctx.lineWidth=3;ctx.strokeStyle=hi;ctx.stroke()}
    if(S.home){const hx=X(S.home.lng),hy=Y(S.home.lat);ctx.beginPath();ctx.moveTo(hx,hy);ctx.lineTo(x,y);ctx.lineWidth=5;ctx.strokeStyle="rgba(0,0,0,.55)";ctx.stroke();ctx.setLineDash([7,6]);ctx.lineWidth=2.5;ctx.strokeStyle="#fff";ctx.stroke();ctx.setLineDash([]);
      const t=homeT(selS);if(t!=null&&isFinite(t)&&Math.hypot(hx-x,hy-y)>70){ctx.font="600 12px 'IBM Plex Mono',monospace";ctx.textAlign="center";label(fmt(t)+" drive",(hx+x)/2,(hy+y)/2,sat?"#fff":"#111")}}
    ctx.beginPath();ctx.arc(x,y,r+9,0,Math.PI*2);ctx.lineWidth=5;ctx.strokeStyle="rgba(0,0,0,.5)";ctx.stroke();ctx.lineWidth=2.5;ctx.strokeStyle=hi;ctx.stroke();
    ctx.font="600 12.5px 'IBM Plex Sans',sans-serif";ctx.textAlign="left";label(selS[0],x+r+14,y+.5,sat?"#fff":"#111");ctx.textAlign="center"}
  if(S.home){const x=X(S.home.lng),y=Y(S.home.lat);ctx.beginPath();ctx.moveTo(x,y);ctx.arc(x,y-20,11,Math.PI*.75,Math.PI*2.25);ctx.closePath();ctx.fillStyle="#111827";ctx.fill();ctx.strokeStyle="#fff";ctx.lineWidth=2;ctx.stroke();
    ctx.fillStyle="#fff";ctx.beginPath();ctx.moveTo(x-6,y-19.5);ctx.lineTo(x,y-25.5);ctx.lineTo(x+6,y-19.5);ctx.lineTo(x+4,y-19.5);ctx.lineTo(x+4,y-14.5);ctx.lineTo(x-4,y-14.5);ctx.lineTo(x-4,y-19.5);ctx.closePath();ctx.fill()}
}

// ---------- INTERACTION ----------
function hitSchool(x,y){let best=-1,bd=COARSE.matches?20:12;SCHOOLS.forEach((s,j)=>{if(!passFilter(s))return;const d=Math.hypot(X(s[5])-x,Y(s[4])-y);if(d<bd){bd=d;best=j}});return best}
// The smallest named neighborhood under the point; a ZIP area only where no named one covers it.
const tip=document.getElementById("tip"),mapCv=map.getCanvas();
map.on("mousemove",e=>{const x=e.point.x,y=e.point.y;
  if(S.placingHome){tip.style.display="none";mapCv.style.cursor="crosshair";return}
  const j=hitSchool(x,y);
  if(j>=0){const s=SCHOOLS[j];tip.textContent=s[0]+(homeT(s)!=null?` · ${fmt(homeT(s))} from home`:"")+(rate(s)?` · rated ${rate(s)}`:"")+(s.students?` · ${s.students} students`:"");mapCv.style.cursor="pointer"}
  else{tip.textContent="";mapCv.style.cursor=""}
  tip.style.left=x+"px";tip.style.top=y+"px";tip.style.display=tip.textContent?"block":"none"});
map.on("mouseout",()=>{tip.style.display="none"});
// On a phone the sheet rises over the lower half of the map, so a tap down there is panned into view.
const reveal=(ll,y)=>{if(MOBILE.matches&&y>innerHeight*.5)map.easeTo({center:[ll.lng,ll.lat],offset:[0,-innerHeight*.23],duration:300})};
map.on("click",e=>{const ll=e.lngLat;
  if(S.placingHome){setHome({lat:+ll.lat.toFixed(5),lng:+ll.lng.toFixed(5)});if(!MOBILE.matches&&app.classList.contains("no-r"))document.getElementById("tgR").click();return}
  const j=hitSchool(e.point.x,e.point.y);if(j>=0){select("sc",j);reveal(ll,e.point.y)}else if(S.sel)select(null)}); // a click on empty map closes the school card
map.on("move",draw);map.on("resize",resize);map.on("load",draw);
document.getElementById("zin").onclick=()=>map.zoomIn();
document.getElementById("zout").onclick=()=>map.zoomOut();
document.getElementById("zfit").onclick=fit;
window.addEventListener("resize",resize);

// ---------- CONTROLS ----------
const LVL={E:"Elementary",M:"Middle",H:"High",K:"K-12 / 6-12"},TYP={pub:"District",chr:"Charter",pvt:"Private"};
// Filter pills on the map: minimum rating, school size and drive limit. Rating and drive are plain drop-downs shaped
// as pills; size is a pill that opens a short list of tick boxes. The drive pill shows only while it does something:
// with the drive-time shading on, or in "From a place".
const pR=document.getElementById("pR"),pD=document.getElementById("pD"),pS=document.getElementById("pS"),pSm=document.getElementById("pSm");
pR.innerHTML=[[0,"Any rating"],[3,"Rated C & up"],[4,"Rated B & up"],[5,"Rated A"]].map(([v,t])=>`<option value="${v}">${t}</option>`).join("");
pD.innerHTML=[3,5,8,10,12,15,20].map(v=>`<option value="${v}">Up to ${v} min drive</option>`).join("");
pSm.innerHTML=SIZES.map(([t],i)=>`<label><input type="checkbox" value="${i}"> ${t} students</label>`).join("");
function sizeLabel(){const k=[...S.size].sort();if(!k.length)return "Any size";if(k.length===1)return "Size: "+SIZES[k[0]][0].toLowerCase();
  if(k.at(-1)-k[0]!==k.length-1)return `Size: ${k.length} ranges`;const lo=SIZES[k[0]][1],hi=SIZES[k.at(-1)][2],f=n=>n.toLocaleString("en-US");
  return k.length===SIZES.length?"Any size":!lo?`Size: under ${f(hi)}`:hi===Infinity?`Size: over ${f(lo)}`:`Size: ${f(lo)}–${f(hi)}`}
function syncPills(){pR.value=S.minR;pD.value=S.sm;pR.classList.toggle("set",S.minR>0);pS.textContent=sizeLabel();pS.classList.toggle("set",S.size.size>0);
  pSm.querySelectorAll("input").forEach(c=>c.checked=S.size.has(+c.value))}
pR.onchange=()=>{S.minR=+pR.value;syncPills();renderAll()};pD.onchange=()=>{S.sm=+pD.value;renderAll()};
pS.onclick=e=>{e.stopPropagation();pSm.classList.toggle("show")};pSm.onclick=e=>e.stopPropagation();
pSm.onchange=e=>{const i=+e.target.value;e.target.checked?S.size.add(i):S.size.delete(i);syncPills();renderAll()};
document.addEventListener("click",()=>pSm.classList.remove("show"));
syncPills();
const badge=t=>`<span class="rt r${t||"N"}" title="State (TEA) rating">${t||"–"}</span>`;
const rb=s=>s[2]==="pvt"?(s.niche?`<span class="rt r${s.niche[0]} rPv" title="Niche grade (private school, not rated by the state)">${s.niche}</span>`:'<span class="rt rP" title="Private school: not rated by the state, no Niche grade">?</span>'):badge(s.tea); // a school's rating badge
function updPlaceUI(){const h=document.getElementById("hint");h.classList.toggle("show",S.placingHome);
  const b=document.getElementById("pH");b.textContent=S.placingHome?"Cancel":S.home?"Move home pin":"Set home pin";b.classList.toggle("set",!!S.home||S.placingHome);document.getElementById("pHx").hidden=!S.home||S.placingHome}
document.getElementById("pH").onclick=()=>{S.placingHome=!S.placingHome;updPlaceUI()};
document.getElementById("pHx").onclick=()=>setHome(null);
document.querySelectorAll("#mode button").forEach(b=>b.onclick=()=>{document.querySelectorAll("#mode button").forEach(x=>x.classList.remove("on"));b.classList.add("on");S.mode=b.dataset.m;recompute();renderAll()});
document.getElementById("lyRd").onchange=e=>{S.lyRd=e.target.checked;draw()};
document.getElementById("lyNm").onchange=e=>{S.lyNm=e.target.checked;draw()};
// Layers: the map key, the switches in Settings and the state stay in step. The key's samples match what is drawn.
const LAYERS=[["nb","lyNb","Neighborhoods",""],["E","lyZE","Elementary"," zones"],["M","lyZM","Middle"," zones"],["H","lyZH","High"," zones"],["zip","lyZip","ZIP areas",""],["iso","lyIso","Drive time",""]];
const line=c=>`<svg class="sw" viewBox="0 0 26 10"><line class="${c}" x1="2" y1="5" x2="24" y2="5"/></svg>`;
const SW={nb:S.nb==="names"?'<span class="sw nbname">Aa</span>':'<svg class="sw" viewBox="0 0 26 10"><rect class="nb" x="2" y="1.5" width="22" height="7" rx="2.5"/></svg>',zip:line("zip"),E:line("zE"),M:line("zM"),H:line("zH"),iso:'<span class="sw grad"></span>'};
const lyGet=k=>k==="nb"?S.lyNb:k==="zip"?S.lyZip:k==="iso"?S.lyIso:S.lyZ[k];
const legend=document.getElementById("legend");
const KEYS={E:"● elementary and K-12",M:"◆ middle &nbsp;● K-12",H:"■ high &nbsp;● K-12"};
legend.innerHTML='<div class="lgrate" title="State (TEA) rating. Colours the school zones and the school markers"><b>Rating</b>'+["A","B","C","D","F"].map(g=>`<span class="rk" style="background:${RC[g]}">${g}</span>`).join("")+'<span class="rk" style="background:#9aa0aa">?</span><span class="rk" style="background:'+PVTC+'">?</span></div>'+
  '<div class="lgkey"><span id="lgshape"></span><br><span class="ring"></span> private, by its Niche grade<br>purple ? private, no grade<br>grey ? public, not rated</div>'+
  '<div class="lgtog">'+["E","M","H"].map(k=>`<button class="lg" data-ly="${k}" title="Show or hide the attendance zones">${SW[k]}Zones</button>`).join("")+`<button class="lg" data-ly="iso" title="Show or hide the drive-time shading">${SW.iso}Drive time</button></div>`+
  '<div class="lgscale" id="lgscale"><span>0</span><span class="bar"></span><span id="lgmax"></span></div>';
document.querySelectorAll("[data-sw]").forEach(e=>e.innerHTML=SW[e.dataset.sw]);
function syncLayers(){for(const [k,id] of LAYERS){document.getElementById(id).checked=lyGet(k);legend.querySelector(`[data-ly="${k}"]`)?.classList.toggle("off",!lyGet(k))}
  document.getElementById("lgscale").classList.toggle("off",!S.lyIso);pD.hidden=!S.lyIso}
function lySet(k,v){if(k==="nb")S.lyNb=v;else if(k==="zip")S.lyZip=v;else if(k==="iso")S.lyIso=v;else S.lyZ[k]=v;syncLayers();draw()}
for(const [k,id] of LAYERS)document.getElementById(id).onchange=e=>lySet(k,e.target.checked);
legend.querySelectorAll(".lg").forEach(b=>b.onclick=()=>lySet(b.dataset.ly,!lyGet(b.dataset.ly)));
syncLayers();
// Two ways to look. "Near schools": start from the schools you chose, shade the map by the drive to the nearest one.
// "From a place": start from a clicked spot, show the drive to each chosen school.
// The level buttons (Elementary, Middle, High) come first: each shows that level's schools (plus K-12 campuses) and zones only.
function syncLvl(){const cur=["E","M","H"].filter(L=>S.levels.has(L));S.lvl=cur.length===3?"all":cur.length===1?cur[0]:"";document.querySelectorAll("#lvl button").forEach(b=>b.classList.toggle("on",b.dataset.l===S.lvl));legend.dataset.lvl=S.lvl;document.getElementById("lgshape").innerHTML=KEYS[S.lvl]||"● elementary &nbsp;◆ middle &nbsp;■ high"} // the map key lists only the chosen level's zones
function setLvl(l){S.levels.clear();for(const L of l==="all"?["E","M","H","K"]:[l,"K"])S.levels.add(L);for(const L of "EMH")S.lyZ[L]=l==="all"?L==="E":L===l;
  syncLvl();syncLayers()}
// Public / Private / Both. Public means district and charter schools together.
function syncTyp(){const pub=S.types.has("pub")&&S.types.has("chr"),none=!S.types.has("pub")&&!S.types.has("chr"),pv=S.types.has("pvt");
  const cur=pub&&pv?"both":pub&&!pv?"pub":none&&pv?"pvt":"";document.querySelectorAll("#typ button").forEach(b=>b.classList.toggle("on",b.dataset.t===cur))}
function setTyp(t){S.types.clear();for(const k of t==="pub"?["pub","chr"]:t==="pvt"?["pvt"]:["pub","chr","pvt"])S.types.add(k);syncTyp()}
document.querySelectorAll("#typ button").forEach(b=>b.onclick=()=>{setTyp(b.dataset.t);renderAll()});syncTyp();
document.querySelectorAll("#lvl button").forEach(b=>b.onclick=()=>{setLvl(b.dataset.l);renderAll()});
{const iso=S.lyIso;setLvl(S.lvl);if(Q.has("z"))for(const L of "EMH")S.lyZ[L]=Q.get("z").includes(L);updPlaceUI();if(Q.has("iso"))S.lyIso=Q.get("iso")!=="0";else S.lyIso=iso;syncLayers()}
// Search by school name. Picking a result zooms to the school and opens its card. If the current level, type or
// minimum rating would hide it, those are changed just enough to show it.
function showSchool(j){const s=SCHOOLS[j];
  if(!passFilter(s)){if(!S.types.has(s[2])){S.types.add(s[2]);syncTyp()}
    const lv=s.serves||(s[1]==="K"?"":s[1]);if(lv&&![...lv].some(L=>S.levels.has(L)))setLvl(lv[0]);
    if(s[2]!=="pvt"&&(RANK[s.tea]||0)<S.minR){S.minR=RANK[s.tea]>=3?RANK[s.tea]:0}
    if(!sizeOK(s))S.size.clear();syncPills()}
  select("sc",j);map.easeTo({center:[s[5],s[4]],zoom:Math.max(map.getZoom(),14),duration:600,offset:MOBILE.matches?[0,-innerHeight*.23]:[0,0]})}
{const q=document.getElementById("q"),box=document.getElementById("qres");let hits=[],act=0;
  const norm=t=>t.normalize("NFD").replace(/[\u0300-\u036f]/g,"").toLowerCase().replace(/[^a-z0-9 ]/g,"");
  const NAMES=SCHOOLS.map(s=>norm(s[0]));
  const show=()=>{box.innerHTML=hits.map((j,i)=>{const s=SCHOOLS[j];return `<div data-j="${j}" class="${i===act?"act":""}">${s[0]} ${rb(s)}<small>${LVL[s[1]]} · grades ${s.grades} · ${s[3]}</small></div>`}).join("")||(q.value.trim().length>1?"<div>No school with that name</div>":"");box.classList.toggle("show",!!box.innerHTML)};
  const pick=j=>{q.value=SCHOOLS[j][0];hits=[];show();q.blur();showSchool(j)};
  q.oninput=()=>{const t=norm(q.value).split(" ").filter(Boolean);act=0;
    hits=t.length&&q.value.trim().length>1?NAMES.map((n,j)=>[j,t.every(w=>n.includes(w))?(n.startsWith(t[0])?0:1):-1]).filter(x=>x[1]>=0).sort((a,b)=>a[1]-b[1]||NAMES[a[0]].localeCompare(NAMES[b[0]])).slice(0,8).map(x=>x[0]):[];show()};
  q.onkeydown=e=>{if(e.key==="ArrowDown"||e.key==="ArrowUp"){if(hits.length){act=(act+(e.key==="ArrowDown"?1:hits.length-1))%hits.length;show()}e.preventDefault()}
    else if(e.key==="Enter"&&hits.length)pick(hits[act]);else if(e.key==="Escape"){q.value="";hits=[];show();q.blur()}};
  q.onfocus=()=>q.oninput();q.onblur=()=>setTimeout(()=>box.classList.remove("show"),150);
  box.onpointerdown=e=>{const d=e.target.closest("[data-j]");if(d){e.preventDefault();pick(+d.dataset.j)}}}
// Basemap
const app=document.querySelector(".app");
function setBase(b){S.base=b;app.classList.toggle("sat",b==="sat");map.setStyle(baseStyle(b));
  document.querySelectorAll("#base button").forEach(x=>x.classList.toggle("on",x.dataset.b===b));document.getElementById("zbase").textContent=b==="sat"?"Map":"Sat";draw()}
document.querySelectorAll("#base button").forEach(b=>b.onclick=()=>setBase(b.dataset.b));
document.getElementById("zbase").onclick=()=>setBase(S.base==="sat"?"map":"sat");
if(S.base!=="sat")setBase(S.base);
// Desktop: the filter panel (left) and the results panel (right) start hidden; two buttons on the map show or hide them.
for(const [id,c] of [["tgL","no-l"],["tgR","no-r"]]){const b=document.getElementById(id);b.onclick=()=>{b.classList.toggle("on",!app.classList.toggle(c));map.resize();resize()}}
// Tabs. Desktop: two tabs in the right panel. Phone: three in the sheet (the third is Settings).
function setTab(p){const set=p==="set";if(!set)S.tab=p;app.classList.toggle("show-set",set);
  document.querySelectorAll(".tabs button").forEach(x=>x.classList.toggle("on",x.dataset.t===S.tab));
  document.querySelectorAll("#mtabs button").forEach(x=>x.classList.toggle("on",x.dataset.p===p));renderList()}
document.querySelectorAll(".tabs button").forEach(b=>b.onclick=()=>setTab(b.dataset.t));
document.querySelectorAll("#mtabs button").forEach(b=>b.onclick=()=>{if(S.sel)select(null);setTab(b.dataset.p);if(sheet.dataset.s==="peek")setSheet("half");document.getElementById("sheetbody").scrollTop=0});
document.getElementById("cardX").onclick=()=>select(null);
// Phone: the panels live in a bottom sheet over a full-screen map. It rests at three heights; drag its header or tap the handle.
const sheet=document.getElementById("sheet"),head=document.getElementById("sheethead");
function setSheet(s){sheet.classList.remove("drag");sheet.style.height="";sheet.dataset.s=s}
let drag=null,dragged=false;
head.addEventListener("pointerdown",e=>{if(MOBILE.matches)drag={y:e.clientY,h:sheet.offsetHeight,moved:false}});
window.addEventListener("pointermove",e=>{if(!drag)return;const dy=drag.y-e.clientY;if(!drag.moved&&Math.abs(dy)<8)return;drag.moved=true;sheet.classList.add("drag");
  sheet.style.height=Math.max(60,Math.min(innerHeight*.92,drag.h+dy))+"px"});
const endDrag=()=>{if(!drag)return;const moved=drag.moved;drag=null;if(!moved)return;dragged=true;setTimeout(()=>dragged=false,60);
  const h=sheet.offsetHeight,vh=innerHeight;setSheet(h<vh*.25?"peek":h<vh*.68?"half":"full")};
window.addEventListener("pointerup",endDrag);window.addEventListener("pointercancel",endDrag);
head.addEventListener("click",e=>{if(dragged){dragged=false;e.stopPropagation();e.preventDefault()}},true);
document.getElementById("grab").onclick=()=>setSheet(sheet.dataset.s==="peek"?"half":"peek");

// ---------- LISTS & CARD ----------
const fmt=t=>t==null?"—":isFinite(t)?Math.round(t)+"′":"—";
// The list as plain text, rebuilt with the list, for the "Copy list" button: one school per line, groups as headings.
let listText=[];
const copyB=document.getElementById("copyL");
copyB.onclick=async()=>{const t=listText.join("\n").trim();let ok=true;
  try{await navigator.clipboard.writeText(t)}catch(e){const a=document.createElement("textarea");a.value=t;a.style.cssText="position:fixed;opacity:0";document.body.appendChild(a);a.select();ok=document.execCommand("copy");a.remove()}
  copyB.textContent=ok?"Copied":"Could not copy";setTimeout(()=>copyB.textContent="Copy list",1600)};
function renderList(){
  listText=[];const grade=s=>s[2]==="pvt"?(s.niche||"no grade"):(s.tea||"not rated");
  const L=document.getElementById("list");L.innerHTML="";const sum=document.getElementById("summary");
  const item=(s,note)=>{const j=SCHOOLS.indexOf(s),t=homeT(s),d=document.createElement("div");d.className="item"+(S.sel&&S.sel.t==="sc"&&S.sel.i===j?" sel":"");
    d.innerHTML=`<div class="nm"><span class="dot" style="background:${LVLC[s[1]]}"></span> ${s[0]} ${rb(s)}</div><div class="num">${t!=null?fmt(t)+"<small>drive</small>":(s.students??"—")+"<small>students</small>"}</div><div class="sm">${s[3]} · grades ${s.grades}${t!=null&&s.students?` · ${s.students} students`:""}${note?` · <b>${note}</b>`:""}</div>`;
    listText.push([s[0],grade(s),t!=null&&isFinite(t)?Math.round(t)+" min drive":null,s[3],"grades "+s.grades,s.students?s.students+" students":null,note||null].filter(Boolean).join(" · "));
    d.onclick=()=>select("sc",j,true);L.appendChild(d)};
  const head=(t,sub)=>{listText.push("",t.toUpperCase());const d=document.createElement("div");d.className="lhead";d.innerHTML=`${t}${sub?`<small>${sub}</small>`:""}`;L.appendChild(d)};
  const empty=t=>{listText.push(t);const d=document.createElement("div");d.className="lnone";d.textContent=t;L.appendChild(d)};
  const byDrive=(a,b)=>homeGrid?homeT(a)-homeT(b):(RANK[rate(b)]||0)-(RANK[rate(a)]||0)||a[0].localeCompare(b[0]);
  // No home pin: every school that passes the filters, best rated first.
  if(!S.home){const rows=SCHOOLS.filter(passFilter).sort(byDrive);
    sum.innerHTML=`<b>${rows.length}</b> schools pass the filters, best rated first. Set a home pin on the map to see only the schools that home can use, by drive time.`;rows.forEach(s=>item(s));return}
  // With a home pin: only the schools that home can use. A home is zoned to one public school per level; public schools it is
  // not zoned for (other zones, other districts) are left out. District schools without a zone, charter schools and private
  // schools take students by application, so they are listed, nearest first. The zoned school shows even when it fails the filters.
  const z=zonedAt(S.home.lat,S.home.lng),lv=["E","M","H"].filter(l=>S.levels.has(l)),dist=(z.E||z.M||z.H||{}).district||null,pub=S.types.has("pub");
  const zoned=lv.map(l=>z[l]).filter(x=>x&&x.sch).map(x=>x.sch);
  const pass=SCHOOLS.filter(s=>passFilter(s)&&!zoned.includes(s)).sort(byDrive);
  const choice=pass.filter(s=>s[2]==="pub"&&!s.zone&&s[3]===dist),chr=pass.filter(s=>s[2]==="chr"),pvt=pass.filter(s=>s[2]==="pvt");
  const left=pass.filter(s=>s[2]==="pub"&&!choice.includes(s)).length;
  sum.innerHTML=`Schools your home pin can use${homeGrid?", nearest first. Minutes are a rough estimate":""}.${left?` <b>${left}</b> public schools pass the filters but are left out: the pin is not zoned for them.`:""}`;
  if(pub){head("Your zoned public school",dist?`${dist}. A place is guaranteed`:"");
    if(zoned.length)zoned.forEach(s=>item(s,passFilter(s)?"":"outside your filters"));else empty(dist?"No zoned school on file at this level.":"No zone data for this spot. Lake Travis, Round Rock and Lago Vista ISDs publish none.");
    if(choice.length){head(`${dist} schools without a zone`,"By application or lottery");choice.forEach(s=>item(s))}
    head("Charter schools","Free, by application or lottery");chr.length?chr.forEach(s=>item(s)):empty("None pass the filters.")}
  if(S.types.has("pvt")){head("Private schools","Tuition, by application");pvt.length?pvt.forEach(s=>item(s)):empty("None pass the filters.")}
}
function select(t,i,center){S.sel=t?{t,i}:null;const mob=MOBILE.matches;if(t&&mob)setSheet("half");
  // a school picked from the list: frame the school together with its attendance zone and the home pin
  if(center&&t==="sc"){const sc=SCHOOLS[i],z=ZONES.find(z=>z.sch===sc),pts=[[sc[4],sc[5]]];if(S.home)pts.push([S.home.lat,S.home.lng]);if(z)for(const p of z.polys)for(const q of p)for(const c of q)pts.push(c);
    if(pts.length>1){const la=pts.map(p=>p[0]),lo=pts.map(p=>p[1]);map.fitBounds([[Math.min(...lo),Math.min(...la)],[Math.max(...lo),Math.max(...la)]],{padding:mob?{top:250,bottom:Math.round(innerHeight*.5),left:30,right:30}:{top:150,bottom:70,left:70,right:70},maxZoom:14,duration:500});center=false}}
  if(center&&t){const ll=[SCHOOLS[i][4],SCHOOLS[i][5]];map.easeTo({center:[ll[1],ll[0]],zoom:Math.max(map.getZoom(),12),duration:400,offset:mob?[0,-innerHeight*.23]:[0,0]})}
  draw();renderList();refreshCard()}
function refreshCard(){const card=document.getElementById("card"),body=document.getElementById("cardBody");sheet.classList.toggle("has-card",!!S.sel);if(!S.sel){card.classList.remove("show");return}
  {const j=S.sel.i,s=SCHOOLS[j];
    const q=encodeURIComponent(`${s[0]} ${s[3]} niche.com`);
    body.innerHTML=`<h3>${s[0]}</h3><div class="meta">${LVL[s[1]]} · grades ${s.grades} · ${s[3]}${s[2]==="chr"?" (charter)":""}<br>${s.address}</div>
    <table>${s[2]==="pvt"?`<tr><td colspan="3">Private school${s.students?`, ${s.students} students`:""} (${s.year?`federal private school survey, ${s.year}`:"listed by Niche, not in the federal survey"}). The state does not rate private schools.</td></tr>`:`<tr><td>State (TEA) rating</td><td class="n">${s.tea?badge(s.tea):"not rated"}</td><td class="n"><a href="https://txschools.gov/?view=school&id=${s.id}" target="_blank" rel="noopener">TXschools</a></td></tr><tr><td>Students</td><td class="n">${s.students??"—"}</td><td class="n">${s.students_year||""}</td></tr>`}
    <tr><td>Niche grade</td><td class="n">${s.niche?`<span class="rt rNi">${s.niche}</span>`:s[2]==="pvt"?"none given":"not entered"}</td><td class="n"><a href="${s.niche_url||"https://www.google.com/search?q="+q}" target="_blank" rel="noopener">${s.niche_url?"Niche":"Find on Niche"}</a></td></tr></table>
    <div class="meta" style="margin-top:8px">${s.zone?"Has an attendance zone. It is shaded on the map when that level's zones are on.":s[2]==="chr"?"Charter school: no attendance zone, admission is by application.":s[2]==="pvt"?"Private school: no attendance zone, admission is by application.":"No attendance zone on file."}</div>
    ${homeT(s)!=null?`<div class="meta">Drive from your home pin: <b>${fmt(homeT(s))}</b> (rough estimate)</div>`:""}`}
  card.classList.add("show")}
function renderAll(){draw();renderList();refreshCard()}

// ---------- BOOT ----------
resize();fit();recompute();renderAll();
