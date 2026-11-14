(() => {
'use strict';

/* =========================================================
   공통 도구
   ========================================================= */
const TAU = Math.PI * 2;
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const lerp = (a, b, t) => a + (b - a) * t;
const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const frac = (x) => x - Math.floor(x);
const hash1 = (n) => frac(Math.sin(n * 127.1 + 311.7) * 43758.5453);

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const seeded = mulberry32(20261114);

// 3차원 값 노이즈 (지구 표면 무늬용)
function h3(x, y, z) {
  let n = (Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(z, 1274126177)) | 0;
  n = Math.imul(n ^ (n >>> 13), 1274126177);
  return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
}
function noise3(x, y, z) {
  const xi = Math.floor(x), yi = Math.floor(y), zi = Math.floor(z);
  let xf = x - xi, yf = y - yi, zf = z - zi;
  xf = xf * xf * (3 - 2 * xf); yf = yf * yf * (3 - 2 * yf); zf = zf * zf * (3 - 2 * zf);
  const a = lerp(h3(xi, yi, zi), h3(xi + 1, yi, zi), xf);
  const b = lerp(h3(xi, yi + 1, zi), h3(xi + 1, yi + 1, zi), xf);
  const c = lerp(h3(xi, yi, zi + 1), h3(xi + 1, yi, zi + 1), xf);
  const d = lerp(h3(xi, yi + 1, zi + 1), h3(xi + 1, yi + 1, zi + 1), xf);
  return lerp(lerp(a, b, yf), lerp(c, d, yf), zf);
}
function fbm(x, y, z, oct) {
  let s = 0, a = 0.5, n = 0;
  for (let i = 0; i < oct; i++) { s += a * noise3(x, y, z); n += a; a *= 0.5; x *= 2.03; y *= 2.03; z *= 2.03; }
  return s / n;
}

// 벡터 · 행렬
const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const norm = (a) => { const l = Math.hypot(a[0], a[1], a[2]) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };
const angleBetween = (a, b) => Math.acos(clamp(dot(a, b), -1, 1));
const mulMV = (m, v) => [m[0] * v[0] + m[1] * v[1] + m[2] * v[2], m[3] * v[0] + m[4] * v[1] + m[5] * v[2], m[6] * v[0] + m[7] * v[1] + m[8] * v[2]];
const mulMTV = (m, v) => [m[0] * v[0] + m[3] * v[1] + m[6] * v[2], m[1] * v[0] + m[4] * v[1] + m[7] * v[2], m[2] * v[0] + m[5] * v[1] + m[8] * v[2]];
function mulMM(a, b) {
  const r = new Array(9);
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++)
    r[i * 3 + j] = a[i * 3] * b[j] + a[i * 3 + 1] * b[3 + j] + a[i * 3 + 2] * b[6 + j];
  return r;
}
function rotAxis(ax, ang) {
  const [x, y, z] = ax, c = Math.cos(ang), s = Math.sin(ang), t = 1 - c;
  return [t * x * x + c, t * x * y - s * z, t * x * z + s * y,
          t * x * y + s * z, t * y * y + c, t * y * z - s * x,
          t * x * z - s * y, t * y * z + s * x, t * z * z + c];
}
function orthonormalize(m) {
  const r0 = norm([m[0], m[1], m[2]]);
  let r1 = [m[3], m[4], m[5]];
  const d = dot(r0, r1);
  r1 = norm([r1[0] - d * r0[0], r1[1] - d * r0[1], r1[2] - d * r0[2]]);
  const r2 = cross(r0, r1);
  return [...r0, ...r1, ...r2];
}

/* =========================================================
   캔버스 · 화면 배치
   ========================================================= */
const canvas = document.getElementById('scene');
const ctx = canvas.getContext('2d');
const panel = document.getElementById('panel');
let W = 0, H = 0, dpr = 1;
let horizonY = 0, shoreBase = 0, swashAmp = 0;
let panelOpen = false;
const view = { cx: 0, cy: 0, R: 0, tx: 0, ty: 0, tR: 0, ready: false };

const EDGE_STEP = 8;
let edge = new Float32Array(0), wet = new Float32Array(0);
let residues = [];
let sandPattern = null;

function computeTarget() {
  const mobile = W < 760;
  let R = mobile ? Math.min(W * 0.3, H * 0.19) : Math.min(W * 0.2, H * 0.25, 240);
  let cx = W / 2, cy = H * 0.47;
  if (panelOpen) {
    if (mobile) {
      const free = H * 0.38;
      R = Math.min(W * 0.24, free * 0.3);
      cy = free * 0.58;
    } else {
      const pw = Math.min(540, W * 0.46) + 22;
      cx = (W - pw) / 2;
      R = Math.min(R, (W - pw) * 0.3);
    }
  }
  view.tx = cx; view.ty = cy; view.tR = R;
  if (!view.ready) { view.cx = cx; view.cy = cy; view.R = R; view.ready = true; }
}

function resize() {
  dpr = Math.min(window.devicePixelRatio || 1, 1.75);
  W = window.innerWidth; H = window.innerHeight;
  canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
  horizonY = H * 0.4; shoreBase = H * 0.69; swashAmp = H * 0.085;
  const n = Math.ceil(W / EDGE_STEP) + 2;
  edge = new Float32Array(n); wet = new Float32Array(n).fill(shoreBase);
  residues = [];
  computeTarget();
  const baseR = W < 760 ? Math.min(W * 0.3, H * 0.19) : Math.min(W * 0.2, H * 0.25, 240);
  ensureGlobeBuf(clamp(Math.round(baseR * 2 * dpr / 2) * 2, 180, 400));
}

function makeSandPattern() {
  const c = document.createElement('canvas'); c.width = c.height = 220;
  const g = c.getContext('2d');
  const r = mulberry32(77);
  for (let i = 0; i < 2600; i++) {
    const v = r();
    g.fillStyle = v < 0.5 ? `rgba(120,85,50,${0.05 + r() * 0.1})` : `rgba(255,245,220,${0.06 + r() * 0.14})`;
    g.fillRect(r() * 220, r() * 220, 1 + r() * 1.4, 1 + r() * 1.4);
  }
  sandPattern = ctx.createPattern(c, 'repeat');
}

/* =========================================================
   하늘 · 해 · 바다 · 모래사장
   ========================================================= */
const SWASH_T = 9.5;          // 파도 한 번이 밀려왔다 빠지는 시간(초)
const RISE = 0.3;             // 주기 중 밀려 올라오는 구간 비율
const clouds = [];
for (let i = 0; i < 9; i++) {
  clouds.push({ x: seeded(), y: 0.3 + seeded() * 0.6, w: 0.12 + seeded() * 0.2, h: 0.018 + seeded() * 0.03, sp: 0.002 + seeded() * 0.004, puffs: 4 + Math.floor(seeded() * 3), seed: seeded() * 100 });
}
const stars = [];
for (let i = 0; i < 60; i++) stars.push([seeded(), seeded() * 0.5, 0.4 + seeded() * 0.9, seeded() * 10]);

function swash(u) {
  if (u < RISE) { const k = 1 - u / RISE; return 1 - k * k * k; }
  const k = (u - RISE) / (1 - RISE);
  return 0.5 + 0.5 * Math.cos(Math.PI * k);
}
function swashPhase(x, t) {
  return frac((t + Math.sin(x * 0.004 + 1) * 0.45 + (x / Math.max(W, 1)) * 0.5) / SWASH_T);
}
function edgeAt(x, t) {
  return shoreBase + swashAmp * swash(swashPhase(x, t)) + Math.sin(x * 0.011 + t * 0.5) * 5 + Math.sin(x * 0.027 - t * 0.33) * 3;
}

function drawSky(t) {
  const hz = horizonY;
  const g = ctx.createLinearGradient(0, 0, 0, hz);
  g.addColorStop(0, '#1b2a5c'); g.addColorStop(0.28, '#3f4f90'); g.addColorStop(0.52, '#8f7aaa');
  g.addColorStop(0.72, '#e48f7c'); g.addColorStop(0.88, '#fbb267'); g.addColorStop(1, '#ffe2a4');
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, hz + 2);

  // 새벽 별
  for (const s of stars) {
    const a = (1 - s[1] / 0.5) * 0.55 * (0.6 + 0.4 * Math.sin(t * 1.3 + s[3]));
    ctx.fillStyle = `rgba(255,255,255,${a.toFixed(3)})`;
    ctx.fillRect(s[0] * W, s[1] * hz, s[2], s[2]);
  }

  // 해 (천천히 떠오른다)
  const sunR = Math.min(W, H) * 0.058;
  const rise = smooth(0, 75, t);
  const sunX = W * 0.76, sunY = hz + sunR * 0.55 - rise * sunR * 1.75;
  ctx.globalCompositeOperation = 'lighter';
  let rg = ctx.createRadialGradient(sunX, sunY, 0, sunX, sunY, Math.max(W, H) * 0.55);
  rg.addColorStop(0, 'rgba(255,225,160,0.75)'); rg.addColorStop(0.12, 'rgba(255,180,105,0.38)');
  rg.addColorStop(0.4, 'rgba(255,120,90,0.12)'); rg.addColorStop(1, 'rgba(255,120,90,0)');
  ctx.fillStyle = rg; ctx.fillRect(0, 0, W, hz + 2);
  ctx.globalCompositeOperation = 'source-over';
  rg = ctx.createRadialGradient(sunX, sunY, 0, sunX, sunY, sunR * 1.12);
  rg.addColorStop(0, '#fffdf0'); rg.addColorStop(0.7, '#fff0b0'); rg.addColorStop(0.9, 'rgba(255,214,120,0.95)'); rg.addColorStop(1, 'rgba(255,200,110,0)');
  ctx.fillStyle = rg; ctx.beginPath(); ctx.arc(sunX, sunY, sunR * 1.12, 0, TAU); ctx.fill();

  // 구름
  for (const c of clouds) {
    const cw = c.w * W, ch = Math.max(5, c.h * H);
    const x = ((c.x + t * c.sp) % 1.3) * (W + cw * 2) / 1.3 * 1.3 - cw;
    const y = c.y * hz;
    const warm = smooth(0.25, 0.95, c.y);
    for (let i = 0; i < c.puffs; i++) {
      const px = x + (i / (c.puffs - 1) - 0.5) * cw * 0.9;
      const pr = cw * (0.22 + hash1(c.seed + i) * 0.18);
      const py = y + (hash1(c.seed + i * 3.3) - 0.5) * ch;
      ctx.save(); ctx.translate(px, py); ctx.scale(1, ch / pr * 1.3);
      const cg = ctx.createRadialGradient(0, 0, 0, 0, 0, pr);
      const r = Math.round(lerp(150, 255, warm)), gg = Math.round(lerp(140, 196, warm)), b = Math.round(lerp(190, 160, warm));
      cg.addColorStop(0, `rgba(${r},${gg},${b},0.5)`); cg.addColorStop(1, `rgba(${r},${gg},${b},0)`);
      ctx.fillStyle = cg; ctx.beginPath(); ctx.arc(0, 0, pr, 0, TAU); ctx.fill(); ctx.restore();
    }
  }
  return { sunX, sunR, rise };
}

function drawStarfish(x, y, r, rot) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  ctx.fillStyle = 'rgba(80,50,30,0.2)'; ctx.beginPath(); ctx.ellipse(2, 3, r, r * 0.9, 0, 0, TAU); ctx.fill();
  ctx.fillStyle = '#f08a5d'; ctx.beginPath();
  for (let i = 0; i < 10; i++) {
    const a = (i / 10) * TAU - Math.PI / 2, rr = i % 2 ? r * 0.42 : r;
    ctx[i ? 'lineTo' : 'moveTo'](Math.cos(a) * rr, Math.sin(a) * rr);
  }
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = 'rgba(255,230,200,0.7)';
  for (let i = 0; i < 5; i++) { const a = (i / 5) * TAU - Math.PI / 2; ctx.beginPath(); ctx.arc(Math.cos(a) * r * 0.45, Math.sin(a) * r * 0.45, r * 0.06, 0, TAU); ctx.fill(); }
  ctx.restore();
}
function drawShell(x, y, r, rot, col) {
  ctx.save(); ctx.translate(x, y); ctx.rotate(rot);
  ctx.fillStyle = 'rgba(80,50,30,0.18)'; ctx.beginPath(); ctx.ellipse(1.5, 2.5, r, r * 0.75, 0, 0, TAU); ctx.fill();
  ctx.fillStyle = col; ctx.beginPath(); ctx.moveTo(0, r * 0.7); ctx.arc(0, 0, r, Math.PI * 0.95, Math.PI * 2.05); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = 'rgba(150,100,80,0.45)'; ctx.lineWidth = 0.8;
  for (let i = -2; i <= 2; i++) { ctx.beginPath(); ctx.moveTo(0, r * 0.7); ctx.lineTo(Math.sin(i * 0.45) * r, -Math.cos(i * 0.45) * r); ctx.stroke(); }
  ctx.restore();
}

function edgePath(offset) {
  ctx.moveTo(0, edge[0] + offset);
  for (let i = 1; i < edge.length; i++) ctx.lineTo(i * EDGE_STEP, edge[i] + offset);
}

let prevU = 0;
function drawSea(t, dt, sun) {
  const hz = horizonY, seaH = shoreBase - hz, shoreMax = shoreBase + swashAmp + 10;
  const uG = frac(t / SWASH_T);

  for (let i = 0; i < edge.length; i++) {
    edge[i] = edgeAt(i * EDGE_STEP, t);
    wet[i] = Math.max(edge[i], wet[i] - dt * H * 0.0045);
  }
  if (prevU < RISE + 0.04 && uG >= RISE + 0.04) residues.push({ y: Float32Array.from(edge), life: 1 });
  prevU = uG;

  // 모래사장
  const sg = ctx.createLinearGradient(0, shoreBase - 20, 0, H);
  sg.addColorStop(0, '#dcbb8c'); sg.addColorStop(0.35, '#ecd2a6'); sg.addColorStop(1, '#d9b684');
  ctx.fillStyle = sg; ctx.fillRect(0, shoreBase - 30, W, H - shoreBase + 30);
  if (sandPattern) { ctx.fillStyle = sandPattern; ctx.fillRect(0, shoreBase - 30, W, H - shoreBase + 30); }
  drawStarfish(W * 0.14, H * 0.855, clamp(W * 0.014, 9, 16), 0.4);
  drawShell(W * 0.3, H * 0.955, clamp(W * 0.009, 6, 11), -0.5, '#fbe6d4');
  drawShell(W * 0.88, H * 0.9, clamp(W * 0.011, 7, 13), 0.3, '#f7cfc0');
  drawShell(W * 0.62, H * 0.965, clamp(W * 0.008, 5, 9), 0.9, '#fff3e2');

  // 젖은 모래 (물이 빠진 자리)
  ctx.beginPath(); edgePath(-2);
  for (let i = wet.length - 1; i >= 0; i--) ctx.lineTo(i * EDGE_STEP, wet[i] + 1);
  ctx.closePath();
  ctx.fillStyle = 'rgba(122,86,52,0.34)'; ctx.fill();
  const wg = ctx.createLinearGradient(0, shoreBase, 0, shoreMax);
  wg.addColorStop(0, 'rgba(255,205,160,0.3)'); wg.addColorStop(1, 'rgba(255,225,190,0.08)');
  ctx.fillStyle = wg; ctx.fill();

  // 남은 거품 자국
  ctx.lineCap = 'round';
  for (const r of residues) {
    r.life -= dt / 7;
    if (r.life <= 0) continue;
    ctx.strokeStyle = `rgba(255,255,255,${(r.life * 0.5).toFixed(3)})`; ctx.lineWidth = 1.6;
    ctx.setLineDash([14, 7, 4, 9]);
    ctx.beginPath(); ctx.moveTo(0, r.y[0]);
    for (let i = 1; i < r.y.length; i++) ctx.lineTo(i * EDGE_STEP, r.y[i]);
    ctx.stroke();
  }
  ctx.setLineDash([]);
  residues = residues.filter((r) => r.life > 0);

  // 바닷물
  ctx.save();
  ctx.beginPath(); ctx.moveTo(0, hz); ctx.lineTo(W, hz);
  for (let i = edge.length - 1; i >= 0; i--) ctx.lineTo(i * EDGE_STEP, edge[i]);
  ctx.closePath();
  const g = ctx.createLinearGradient(0, hz, 0, shoreMax);
  g.addColorStop(0, '#dc9c7c'); g.addColorStop(0.05, '#a48a9c'); g.addColorStop(0.2, '#4f79a3');
  g.addColorStop(0.48, '#22688e'); g.addColorStop(0.7, '#2a909e'); g.addColorStop(0.82, 'rgba(70,176,176,0.86)');
  g.addColorStop(1, 'rgba(140,220,208,0.3)');
  ctx.fillStyle = g; ctx.fill();
  ctx.clip();

  // 물결
  const ROWS = 30, sh = t * 0.045 * ROWS, base = Math.floor(sh), fr = sh - base;
  for (let j = 0; j < ROWS; j++) {
    const d = (j + fr) / ROWS, id = j - base;
    const y = hz + Math.pow(d, 2.1) * seaH * 1.08;
    const amp = 0.4 + d * d * 6, wl = 30 + d * 190, ph = hash1(id * 1.7) * 100;
    const a = (0.04 + 0.17 * d) * smooth(0, 0.08, d) * (1 - smooth(0.86, 1, d));
    ctx.beginPath();
    for (let x = -10; x <= W + 14; x += 14) {
      const yy = y + Math.sin(x / wl + ph + t * 0.5) * amp + Math.sin(x / (wl * 0.31) + ph * 1.3 - t * 0.8) * amp * 0.35;
      if (x === -10) ctx.moveTo(x, yy); else ctx.lineTo(x, yy);
    }
    ctx.strokeStyle = `rgba(255,255,255,${a.toFixed(3)})`; ctx.lineWidth = 0.6 + d * 1.8; ctx.stroke();
    ctx.save(); ctx.translate(0, 1.5 + d * 3.5);
    ctx.strokeStyle = `rgba(8,40,80,${(a * 0.9).toFixed(3)})`; ctx.stroke(); ctx.restore();
  }

  // 햇빛 반사
  ctx.globalCompositeOperation = 'lighter';
  ctx.save(); ctx.translate(sun.sunX, hz); ctx.scale(1, (seaH * 1.15) / (W * 0.17));
  const rg = ctx.createRadialGradient(0, 0, 0, 0, 0, W * 0.17);
  rg.addColorStop(0, 'rgba(255,196,125,0.6)'); rg.addColorStop(0.5, 'rgba(255,160,100,0.16)'); rg.addColorStop(1, 'rgba(255,150,90,0)');
  ctx.fillStyle = rg; ctx.beginPath(); ctx.arc(0, 0, W * 0.17, 0, Math.PI); ctx.fill(); ctx.restore();
  for (let i = 0; i < 80; i++) {
    const f = i / 79, y = hz + 1 + Math.pow(f, 1.7) * seaH * 1.1, hw = sun.sunR * 0.6 + f * W * 0.07;
    for (let k = 0; k < 3; k++) {
      const ph = hash1(i * 7.3 + k * 13.1);
      const x = sun.sunX + (hash1(i * 3.1 + k * 5.7) - 0.5) * 2 * hw + Math.sin(t * 0.7 + ph * 20) * hw * 0.15;
      const a = (0.15 + 0.85 * Math.pow(Math.abs(Math.sin(t * (1.5 + ph * 2.5) + ph * 30)), 2)) * (0.6 - f * 0.42);
      const w = (5 + f * 30) * (0.5 + ph), hh = 0.9 + f * 1.5;
      ctx.fillStyle = `rgba(255,${Math.round(205 + ph * 30)},150,${a.toFixed(3)})`;
      ctx.beginPath(); ctx.ellipse(x, y, w / 2, hh, 0, 0, TAU); ctx.fill();
    }
  }
  ctx.globalCompositeOperation = 'source-over';

  // 수평선 안개
  const hg = ctx.createLinearGradient(0, hz, 0, hz + seaH * 0.08);
  hg.addColorStop(0, 'rgba(255,225,185,0.55)'); hg.addColorStop(1, 'rgba(255,225,185,0)');
  ctx.fillStyle = hg; ctx.fillRect(0, hz, W, seaH * 0.08);

  // 부서지며 다가오는 파도
  if (uG > 0.72) {
    const k = (uG - 0.72) / 0.28;
    ctx.beginPath();
    for (let i = 0; i < edge.length; i++) {
      const x = i * EDGE_STEP;
      const y = edge[i] - (1 - k) * H * 0.075 - 4 + Math.sin(x * 0.02 + t) * 3;
      if (!i) ctx.moveTo(x, y); else ctx.lineTo(x, y);
    }
    ctx.strokeStyle = `rgba(255,255,255,${(0.2 + k * 0.6).toFixed(3)})`; ctx.lineWidth = 2 + k * 9; ctx.stroke();
    ctx.save(); ctx.translate(0, 4 + k * 7);
    ctx.strokeStyle = `rgba(10,60,90,${(k * 0.22).toFixed(3)})`; ctx.lineWidth = 3 + k * 5; ctx.stroke(); ctx.restore();
  }

  // 얕은 물 위 거품 무늬
  const rushK = uG < RISE ? Math.pow(uG / RISE, 0.6) : Math.max(0, 1 - (uG - RISE) / 0.45);
  for (let n = 1; n <= 3; n++) {
    ctx.setLineDash([20 + n * 6, 12, 5, 16 + n * 4]); ctx.lineDashOffset = t * 12 * (n % 2 ? 1 : -1) + n * 37;
    ctx.strokeStyle = `rgba(255,255,255,${(0.1 + 0.26 * rushK - n * 0.03).toFixed(3)})`; ctx.lineWidth = 2.4 - n * 0.4;
    ctx.beginPath();
    for (let i = 0; i < edge.length; i++) {
      const x = i * EDGE_STEP, y = edge[i] - n * (9 + rushK * 7) + Math.sin(x * 0.03 + t * 0.8 + n * 2) * 3.5;
      if (!i) ctx.moveTo(x, y); else ctx.lineTo(x, y);
    }
    ctx.stroke();
  }
  ctx.setLineDash([]);
  ctx.restore();

  // 물가의 흰 거품
  const fw = 3 + 8 * rushK;
  ctx.lineJoin = 'round';
  ctx.strokeStyle = `rgba(255,255,255,${(0.28 + 0.2 * rushK).toFixed(3)})`; ctx.lineWidth = fw * 2;
  ctx.beginPath(); edgePath(-fw * 0.9); ctx.stroke();
  ctx.strokeStyle = 'rgba(255,255,255,0.92)'; ctx.lineWidth = fw * 0.55 + 1;
  ctx.beginPath(); edgePath(-1); ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,0.8)';
  for (let i = 0; i < edge.length; i += 2) {
    const hsh = hash1(i * 5.1 + Math.floor(t * 2 + i * 0.37));
    if (hsh > 0.5) { ctx.beginPath(); ctx.arc(i * EDGE_STEP + hsh * 9, edge[i] - 4 - hsh * fw * 2.4, 0.8 + hsh * 1.5, 0, TAU); ctx.fill(); }
  }
  return uG;
}

/* =========================================================
   3D 지구 (구면 텍스처를 직접 계산해 그림)
   ========================================================= */
const TW = 1024, TH = 512, SEA = 0.5;
const tex = new Uint8ClampedArray(TW * TH * 4);
const cloudTex = new Uint8Array(TW * TH);
const heightAt = (x, y, z) => fbm(x * 1.7 + 11.3, y * 1.7 + 5.1, z * 1.7 - 7.7, 5);
const mix3 = (a, b, t) => [lerp(a[0], b[0], t), lerp(a[1], b[1], t), lerp(a[2], b[2], t)];

function buildTextures() {
  for (let v = 0; v < TH; v++) {
    const lat = (0.5 - (v + 0.5) / TH) * Math.PI, cl = Math.cos(lat), sl = Math.sin(lat);
    for (let u = 0; u < TW; u++) {
      const lon = ((u + 0.5) / TW - 0.5) * TAU;
      const x = cl * Math.cos(lon), y = sl, z = cl * Math.sin(lon);
      const h = heightAt(x, y, z), detail = noise3(x * 9 + 3, y * 9, z * 9);
      let c, ocean = 0;
      if (Math.abs(lat) > 1.22 + (detail - 0.5) * 0.4) c = [240, 247, 255];
      else if (h < SEA) {
        const d = SEA - h; ocean = 255;
        c = mix3([78, 196, 218], [30, 116, 196], smooth(0, 0.045, d));
        c = mix3(c, [14, 58, 138], smooth(0.045, 0.16, d));
      } else {
        const e = h - SEA;
        c = mix3([240, 224, 166], [132, 204, 84], smooth(0.008, 0.022, e));
        c = mix3(c, [62, 154, 74], smooth(0.03, 0.085, e));
        c = mix3(c, [150, 140, 104], smooth(0.1, 0.14, e));
        c = mix3(c, [246, 249, 253], smooth(0.15, 0.19, e));
        const k = 0.9 + detail * 0.2; c = [c[0] * k, c[1] * k, c[2] * k];
      }
      const i = (v * TW + u) * 4;
      tex[i] = c[0]; tex[i + 1] = c[1]; tex[i + 2] = c[2]; tex[i + 3] = ocean;
      const cn = fbm(x * 2.3 + 40, y * 3.4 + 17, z * 2.3 - 9, 4);
      cloudTex[v * TW + u] = smooth(0.56, 0.7, cn) * 235;
    }
  }
}

let gbuf = null, gctx = null, gimg = null, gD = 0;
function ensureGlobeBuf(D) {
  if (D === gD) return;
  gD = D; gbuf = document.createElement('canvas'); gbuf.width = gbuf.height = D;
  gctx = gbuf.getContext('2d'); gimg = gctx.createImageData(D, D);
}
const LIGHT = norm([-0.5, 0.55, 0.68]);
const HALF = norm([LIGHT[0], LIGHT[1], LIGHT[2] + 1]);

function renderGlobe(M, cloudShift) {
  const D = gD, Rb = D / 2, data = gimg.data;
  const m0 = M[0], m1 = M[1], m2 = M[2], m3 = M[3], m4 = M[4], m5 = M[5], m6 = M[6], m7 = M[7], m8 = M[8];
  const invTau = 1 / TAU, invPi = 1 / Math.PI;
  for (let py = 0; py < D; py++) {
    const y = -(py + 0.5 - Rb) / Rb, yy = y * y;
    for (let px = 0; px < D; px++) {
      const i = (py * D + px) * 4;
      const x = (px + 0.5 - Rb) / Rb, d2 = x * x + yy;
      if (d2 >= 1) { data[i + 3] = 0; continue; }
      const z = Math.sqrt(1 - d2);
      const lx = m0 * x + m3 * y + m6 * z;
      let ly = m1 * x + m4 * y + m7 * z;
      const lz = m2 * x + m5 * y + m8 * z;
      if (ly > 1) ly = 1; else if (ly < -1) ly = -1;
      let tu = ((Math.atan2(lz, lx) * invTau + 0.5) * TW) | 0;
      let tv = ((0.5 - Math.asin(ly) * invPi) * TH) | 0;
      if (tu >= TW) tu = TW - 1; else if (tu < 0) tu = 0;
      if (tv >= TH) tv = TH - 1; else if (tv < 0) tv = 0;
      const ti = (tv * TW + tu) * 4;
      let r = tex[ti], g = tex[ti + 1], b = tex[ti + 2];
      const ca = cloudTex[tv * TW + ((tu + cloudShift) % TW)] * 0.0036;
      let diff = x * LIGHT[0] + y * LIGHT[1] + z * LIGHT[2]; if (diff < 0) diff = 0;
      const shade = 0.42 + 0.74 * diff;
      let spec = 0;
      if (tex[ti + 3]) { const nh = x * HALF[0] + y * HALF[1] + z * HALF[2]; if (nh > 0.9) spec = Math.pow(nh, 46) * 150 * (1 - ca); }
      r = (r + (255 - r) * ca) * shade + spec;
      g = (g + (255 - g) * ca) * shade + spec;
      b = (b + (255 - b) * ca) * shade + spec;
      const rim = (1 - z) * (1 - z) * (1 - z);
      data[i] = r + (150 - r) * rim * 0.75 + 70 * rim;
      data[i + 1] = g + (200 - g) * rim * 0.75 + 40 * rim;
      data[i + 2] = b + (255 - b) * rim * 0.75;
      data[i + 3] = d2 > 0.96 ? clamp((1 - Math.sqrt(d2)) * Rb, 0, 1) * 255 : 255;
    }
  }
  gctx.putImageData(gimg, 0, 0);
}

/* =========================================================
   지구 위 친구들 (남자아이 · 강아지 · 고양이 · 꽃 · 나무)
   ========================================================= */
let M = [1, 0, 0, 0, 1, 0, 0, 0, 1];           // 지구 좌표 → 화면 좌표 회전
const BOY_VIEW = norm([0, 0.72, 0.69]);        // 아이가 머무는 화면상 위치(지구 윗부분)

function tangentAt(p) {
  const up = Math.abs(p[1]) > 0.9 ? [1, 0, 0] : [0, 1, 0];
  return norm(cross(up, p));
}
function makeCritter(kind, p, base) {
  return { kind, p: norm(p), h: tangentAt(norm(p)), base, speed: 0, face: 1, phase: 0, jump: 0, vj: 0, state: 'wander', timer: 1 + Math.random() * 2, wturn: 0, target: null };
}
const house = { p: norm([-0.15, 0.74, 0.65]) };
const boy = makeCritter('boy', BOY_VIEW, 0.5);
const dog = makeCritter('dog', norm([0.35, 0.75, 0.56]), 0.52);
const cat = makeCritter('cat', norm([-0.38, 0.7, 0.6]), 0.44);
boy.state = 'run'; boy.timer = 3;

function stepMove(c, dt) {
  const a = c.speed * dt;
  if (a) {
    const ca = Math.cos(a), sa = Math.sin(a), p = c.p, h = c.h;
    c.p = norm([p[0] * ca + h[0] * sa, p[1] * ca + h[1] * sa, p[2] * ca + h[2] * sa]);
    c.h = [h[0] * ca - p[0] * sa, h[1] * ca - p[1] * sa, h[2] * ca - p[2] * sa];
  }
  const d = dot(c.h, c.p);
  c.h = norm([c.h[0] - d * c.p[0], c.h[1] - d * c.p[1], c.h[2] - d * c.p[2]]);
  c.phase += c.speed * dt * 24;
  if (c.jump > 0 || c.vj > 0) { c.jump += c.vj * dt; c.vj -= 7.5 * dt; if (c.jump <= 0) { c.jump = 0; c.vj = 0; } }
}
function turn(c, ang) {
  const s = cross(c.p, c.h), ca = Math.cos(ang), sa = Math.sin(ang);
  c.h = norm([c.h[0] * ca + s[0] * sa, c.h[1] * ca + s[1] * sa, c.h[2] * ca + s[2] * sa]);
}
function steerTo(c, q, maxTurn) {
  const k = dot(q, c.p);
  const d = [q[0] - k * c.p[0], q[1] - k * c.p[1], q[2] - k * c.p[2]];
  if (Math.hypot(d[0], d[1], d[2]) < 1e-4) return;
  const dn = norm(d);
  const ang = Math.atan2(dot(c.p, cross(c.h, dn)), dot(c.h, dn));
  turn(c, clamp(ang, -maxTurn, maxTurn));
}
function wander(c, dt, amount) {
  c.wturn += (Math.random() - 0.5) * dt * amount;
  c.wturn *= Math.pow(0.35, dt);
  turn(c, c.wturn * dt);
}
const hop = (c, v) => { if (c.jump === 0) c.vj = v; };

// 조작
const keys = new Set();
let aiMode = true, lastInput = -99;
function boyUpdate(dt, t) {
  const kx = (keys.has('ArrowRight') ? 1 : 0) - (keys.has('ArrowLeft') ? 1 : 0);
  const ky = (keys.has('ArrowUp') ? 1 : 0) - (keys.has('ArrowDown') ? 1 : 0);
  if (kx || ky) {
    lastInput = t;
    const vB = mulMV(M, boy.p);
    let d = [kx, ky * 0.35, -ky];
    const k = dot(d, vB);
    d = norm([d[0] - k * vB[0], d[1] - k * vB[1], d[2] - k * vB[2]]);
    boy.h = mulMTV(M, d);
    boy.speed = 0.58;
  } else if (aiMode && t - lastInput > 2.2) {
    boy.timer -= dt;
    if (boy.timer <= 0) {
      if (boy.state === 'run' && Math.random() < 0.45) { boy.state = 'idle'; boy.timer = 0.7 + Math.random() * 1.6; }
      else { boy.state = 'run'; boy.timer = 2.5 + Math.random() * 4; boy.wturn = (Math.random() - 0.5) * 2.4; }
      if (Math.random() < 0.4) hop(boy, 1.9);
    }
    if (boy.state === 'run') { wander(boy, dt, 5); boy.speed = boy.base; } else boy.speed = 0;
  } else boy.speed = 0;
  stepMove(boy, dt);
}

const LEASH = 0.78;
function animalUpdate(c, dt) {
  c.timer -= dt;
  if (c.timer <= 0) {
    const r = Math.random();
    if (r < 0.42) { c.state = 'wander'; c.timer = 2 + Math.random() * 3; c.wturn = (Math.random() - 0.5) * 3; }
    else if (r < 0.76) { c.state = 'chase'; c.timer = 3 + Math.random() * 3; c.target = c.kind === 'dog' ? (Math.random() < 0.7 ? boy : cat) : (Math.random() < 0.55 ? dog : boy); }
    else { c.state = 'idle'; c.timer = 1 + Math.random() * (c.kind === 'cat' ? 3.5 : 2); }
    if (Math.random() < 0.35) hop(c, 1.7);
  }
  const far = angleBetween(c.p, boy.p);
  if (far > LEASH) { steerTo(c, boy.p, 5 * dt); c.speed = Math.max(c.base * 1.5, 0.72); }
  else if (c.state === 'wander') { wander(c, dt, 6); c.speed = c.base; }
  else if (c.state === 'chase') {
    if (angleBetween(c.p, c.target.p) < 0.24) { c.state = 'idle'; c.timer = 0.8 + Math.random() * 1.4; c.speed = 0; if (Math.random() < 0.6) hop(c, 1.6); }
    else { steerTo(c, c.target.p, 5 * dt); c.speed = c.base * 1.35; }
  } else c.speed = 0;
  stepMove(c, dt);
  // 서로 겹쳐 서지 않도록 살짝 밀어낸다
  for (const o of [boy, dog, cat]) {
    if (o === c) continue;
    const gap = angleBetween(c.p, o.p);
    if (gap < 0.2) {
      const k = dot(c.p, o.p);
      let away = [c.p[0] - k * o.p[0], c.p[1] - k * o.p[1], c.p[2] - k * o.p[2]];
      if (Math.hypot(away[0], away[1], away[2]) < 1e-4) away = c.h;
      away = norm(away);
      const push = (0.2 - gap) * Math.min(1, dt * 6);
      c.p = norm([c.p[0] + away[0] * push, c.p[1] + away[1] * push, c.p[2] + away[2] * push]);
      const d = dot(c.h, c.p);
      c.h = norm([c.h[0] - d * c.p[0], c.h[1] - d * c.p[1], c.h[2] - d * c.p[2]]);
    }
  }
}

// 꽃 · 나무 심기 (땅 위에만)
const FLOWER_COLORS = ['#ff7eb6', '#ff5a6e', '#ffd166', '#b388eb', '#ffffff', '#ff9f43', '#ff8fa3', '#7fd3ff'];
const flowers = [], trees = [];
function plant() {
  let guard = 0;
  while ((flowers.length < 80 || trees.length < 9) && guard++ < 20000) {
    const y = seeded() * 1.7 - 0.85, a = seeded() * TAU, r = Math.sqrt(1 - y * y);
    const p = [r * Math.cos(a), y, r * Math.sin(a)];
    const e = heightAt(p[0], p[1], p[2]) - SEA;
    if (e < 0.02 || e > 0.095) continue;
    if (angleBetween(p, house.p) < 0.16) continue;
    if (trees.length < 9 && seeded() < 0.1) trees.push({ p, s: 0.8 + seeded() * 0.5, ph: seeded() * 10 });
    else if (flowers.length < 80) flowers.push({ p, col: FLOWER_COLORS[Math.floor(seeded() * FLOWER_COLORS.length)], type: seeded() < 0.3 ? 1 : 0, s: 0.75 + seeded() * 0.6, ph: seeded() * 10 });
  }
}

/* ---------- 그리기 도우미 ---------- */
function ell(x, y, rx, ry) { ctx.beginPath(); ctx.ellipse(x, y, Math.max(rx, 0.001), Math.max(ry, 0.001), 0, 0, TAU); ctx.fill(); }
function circ(x, y, r) { ctx.beginPath(); ctx.arc(x, y, r, 0, TAU); ctx.fill(); }
function line(x1, y1, x2, y2) { ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); }

function drawFlower(f, t) {
  const sway = Math.sin(t * 1.6 + f.ph) * 0.08;
  ctx.lineCap = 'round';
  ctx.strokeStyle = '#2f8f46'; ctx.lineWidth = 0.09;
  ctx.beginPath(); ctx.moveTo(0, 0); ctx.quadraticCurveTo(0, -0.4, sway, -0.72); ctx.stroke();
  ctx.fillStyle = '#3fa652'; ctx.beginPath(); ctx.ellipse(0.13, -0.28, 0.14, 0.06, -0.5, 0, TAU); ctx.fill();
  ctx.fillStyle = f.col;
  if (f.type === 1) {       // 튤립
    ctx.beginPath(); ctx.moveTo(sway - 0.2, -1.02); ctx.quadraticCurveTo(sway - 0.24, -0.66, sway, -0.66);
    ctx.quadraticCurveTo(sway + 0.24, -0.66, sway + 0.2, -1.02); ctx.lineTo(sway + 0.08, -0.88); ctx.lineTo(sway, -1.06); ctx.lineTo(sway - 0.08, -0.88); ctx.closePath(); ctx.fill();
  } else {                  // 다섯 꽃잎
    for (let i = 0; i < 5; i++) { const a = (i / 5) * TAU + f.ph; circ(sway + Math.cos(a) * 0.19, -0.8 + Math.sin(a) * 0.19, 0.15); }
    ctx.fillStyle = f.col === '#ffd166' ? '#ff8c42' : '#ffd84d'; circ(sway, -0.8, 0.11);
  }
}
function drawTree(tr, t) {
  const sw = Math.sin(t * 1.1 + tr.ph) * 0.02;
  ctx.fillStyle = 'rgba(20,40,30,0.2)'; ell(0, 0, 0.3, 0.06);
  ctx.fillStyle = '#8a5a35'; ctx.beginPath(); ctx.moveTo(-0.07, 0); ctx.lineTo(-0.045, -0.5); ctx.lineTo(0.045, -0.5); ctx.lineTo(0.07, 0); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#2f9d58'; circ(-0.17 + sw, -0.58, 0.22); circ(0.18 + sw, -0.6, 0.21);
  ctx.fillStyle = '#43b96a'; circ(sw * 1.5, -0.8, 0.27);
  ctx.fillStyle = 'rgba(255,255,255,0.18)'; circ(-0.08 + sw * 1.5, -0.88, 0.1);
}

function drawHouse(h, t) {
  // 1. 부드러운 지면 그림자
  ctx.fillStyle = 'rgba(15, 30, 45, 0.28)';
  ell(0, 0.02, 0.58, 0.12);

  // 2. 집 앞마당 디딤돌
  ctx.fillStyle = '#bda891';
  ell(-0.02, 0.04, 0.09, 0.04);
  ell(0.08, 0.07, 0.07, 0.035);
  ell(-0.11, 0.08, 0.06, 0.03);

  // 3. 본체 기단
  ctx.fillStyle = '#b39c82';
  ctx.fillRect(-0.34, -0.06, 0.68, 0.06);

  // 4. 벽체 본체 (따스한 크림색 스투코 외벽)
  const wg = ctx.createLinearGradient(-0.33, -0.6, 0.33, 0);
  wg.addColorStop(0, '#fffcf5');
  wg.addColorStop(0.5, '#faedd9');
  wg.addColorStop(1, '#ebd7bf');
  ctx.fillStyle = wg;
  ctx.fillRect(-0.33, -0.54, 0.66, 0.48);

  // 모퉁이 원목 기둥 & 가로 보
  ctx.fillStyle = '#9b714b';
  ctx.fillRect(-0.34, -0.54, 0.04, 0.54);
  ctx.fillRect(0.3, -0.54, 0.04, 0.54);
  ctx.fillRect(-0.34, -0.54, 0.68, 0.035);

  // 5. 원목 아치형 문
  ctx.save();
  ctx.translate(-0.13, 0);
  ctx.fillStyle = '#7a4b2c';
  ctx.beginPath();
  ctx.moveTo(-0.11, 0); ctx.lineTo(-0.11, -0.27);
  ctx.arc(0, -0.27, 0.11, Math.PI, 0);
  ctx.lineTo(0.11, 0); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#a66d43';
  ctx.beginPath();
  ctx.moveTo(-0.09, 0); ctx.lineTo(-0.09, -0.27);
  ctx.arc(0, -0.27, 0.09, Math.PI, 0);
  ctx.lineTo(0.09, 0); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = '#6e3f20'; ctx.lineWidth = 0.015;
  line(-0.03, -0.34, -0.03, 0);
  line(0.03, -0.34, 0.03, 0);
  ctx.fillStyle = '#ffd166'; circ(0.055, -0.15, 0.022);
  ctx.fillStyle = '#4a2810'; circ(0.055, -0.15, 0.009);
  ctx.restore();

  // 문 옆 벽걸이 등불
  const lampGlow = 0.8 + 0.2 * Math.sin(t * 3.5);
  ctx.strokeStyle = '#3a2518'; ctx.lineWidth = 0.018;
  line(-0.25, -0.32, -0.21, -0.35);
  line(-0.21, -0.35, -0.21, -0.3);
  ctx.fillStyle = `rgba(255, 215, 80, ${(0.35 * lampGlow).toFixed(2)})`; circ(-0.21, -0.27, 0.08);
  ctx.fillStyle = '#ffe066'; circ(-0.21, -0.27, 0.025);

  // 6. 앞 창문 (따스한 호박색 불빛 창문 + 꽃상자)
  ctx.save();
  ctx.translate(0.14, -0.28);
  ctx.fillStyle = '#7a4b2c';
  ctx.beginPath(); ctx.arc(0, 0, 0.105, 0, TAU); ctx.fill();
  const lg = ctx.createRadialGradient(0, 0, 0, 0, 0, 0.085);
  lg.addColorStop(0, '#ffffff');
  lg.addColorStop(0.5, '#ffe57f');
  lg.addColorStop(1, '#f7b05b');
  ctx.fillStyle = lg;
  ctx.beginPath(); ctx.arc(0, 0, 0.085, 0, TAU); ctx.fill();
  ctx.strokeStyle = '#6e3f20'; ctx.lineWidth = 0.016;
  line(-0.085, 0, 0.085, 0); line(0, -0.085, 0, 0.085);
  ctx.fillStyle = '#8a5a35'; ctx.fillRect(-0.11, 0.09, 0.22, 0.05);
  ctx.fillStyle = '#3ca354';
  circ(-0.08, 0.08, 0.025); circ(-0.03, 0.075, 0.028); circ(0.03, 0.078, 0.026); circ(0.08, 0.08, 0.025);
  ctx.fillStyle = '#ff6b8b'; circ(-0.07, 0.07, 0.018);
  ctx.fillStyle = '#ffd166'; circ(0, 0.065, 0.018);
  ctx.fillStyle = '#ff8fa3'; circ(0.07, 0.07, 0.018);
  ctx.restore();

  // 7. 상단 박공벽 & 다락방 작은 둥근 창
  ctx.fillStyle = '#faedd9';
  ctx.beginPath();
  ctx.moveTo(-0.33, -0.54);
  ctx.lineTo(0, -0.84);
  ctx.lineTo(0.33, -0.54);
  ctx.closePath();
  ctx.fill();
  ctx.fillStyle = '#7a4b2c'; circ(0, -0.63, 0.055);
  ctx.fillStyle = '#fff099'; circ(0, -0.63, 0.04);
  ctx.strokeStyle = '#6e3f20'; ctx.lineWidth = 0.012;
  line(-0.04, -0.63, 0.04, -0.63); line(0, -0.67, 0, -0.59);

  // 8. 굴뚝과 별빛 연기
  ctx.save();
  ctx.translate(0.18, -0.68);
  ctx.fillStyle = '#a17a5e'; ctx.fillRect(0, -0.22, 0.09, 0.26);
  ctx.fillStyle = '#7d583f'; ctx.fillRect(-0.015, -0.25, 0.12, 0.035);
  ctx.strokeStyle = '#6a4730'; ctx.lineWidth = 0.01;
  line(0, -0.15, 0.09, -0.15); line(0, -0.07, 0.09, -0.07);
  line(0.045, -0.22, 0.045, -0.15); line(0.045, -0.07, 0.045, 0);

  for (let i = 0; i < 4; i++) {
    const p = frac(t * 0.35 + i * 0.25);
    const py = -0.26 - p * 0.45;
    const px = 0.045 + Math.sin(t * 1.8 + i * 2) * 0.04 * p;
    const pr = 0.03 + p * 0.065;
    const alpha = (Math.sin(p * Math.PI) * 0.55).toFixed(2);
    ctx.fillStyle = `rgba(255, 248, 230, ${alpha})`;
    circ(px, py, pr);
    if (p > 0.25 && p < 0.75) {
      ctx.fillStyle = `rgba(255, 220, 100, ${alpha})`;
      circ(px, py, 0.012);
    }
  }
  ctx.restore();

  // 9. 동화풍 곡선형 테라코타 지붕
  const rg = ctx.createLinearGradient(-0.4, -0.9, 0.4, -0.5);
  rg.addColorStop(0, '#f27663');
  rg.addColorStop(0.35, '#e05340');
  rg.addColorStop(1, '#be3827');
  ctx.fillStyle = rg;

  ctx.beginPath();
  ctx.moveTo(0, -0.88);
  ctx.quadraticCurveTo(0.2, -0.78, 0.39, -0.52);
  ctx.lineTo(-0.39, -0.52);
  ctx.quadraticCurveTo(-0.2, -0.78, 0, -0.88);
  ctx.closePath();
  ctx.fill();

  ctx.fillStyle = 'rgba(60, 20, 15, 0.22)';
  ctx.fillRect(-0.34, -0.54, 0.68, 0.03);

  ctx.strokeStyle = 'rgba(255, 255, 255, 0.26)';
  ctx.lineWidth = 0.015;
  for (let r = 1; r <= 3; r++) {
    const k = r / 4;
    const y1 = lerp(-0.84, -0.53, k);
    const w1 = lerp(0.08, 0.35, k);
    ctx.beginPath();
    ctx.moveTo(-w1, y1);
    ctx.quadraticCurveTo(0, y1 + 0.02, w1, y1);
    ctx.stroke();
  }

  // 10. 지붕 꼭대기 어린왕자의 황금별
  ctx.save();
  ctx.translate(0, -0.88);
  ctx.strokeStyle = '#ffd166'; ctx.lineWidth = 0.018; line(0, 0, 0, -0.1);
  ctx.translate(0, -0.11);
  const starPulse = 0.85 + 0.22 * Math.sin(t * 3.2);
  ctx.scale(starPulse, starPulse);
  ctx.fillStyle = 'rgba(255, 230, 120, 0.38)'; circ(0, 0, 0.08);
  ctx.fillStyle = '#ffcf3a';
  ctx.beginPath();
  for (let i = 0; i < 8; i++) {
    const a = (i / 8) * TAU - Math.PI / 2;
    const r = i % 2 ? 0.025 : 0.065;
    ctx[i ? 'lineTo' : 'moveTo'](Math.cos(a) * r, Math.sin(a) * r);
  }
  ctx.closePath(); ctx.fill();
  ctx.restore();

  // 11. 어린왕자의 상징: 유리 돔 속의 붉은 장미
  ctx.save();
  ctx.translate(0.44, 0);
  ctx.fillStyle = '#8a5a35'; ctx.fillRect(-0.06, -0.09, 0.12, 0.09);
  ctx.fillStyle = '#6e4425'; ctx.fillRect(-0.07, -0.11, 0.14, 0.025);
  ctx.strokeStyle = '#2f8f46'; ctx.lineWidth = 0.016;
  ctx.beginPath(); ctx.moveTo(0, -0.11); ctx.quadraticCurveTo(0.02, -0.17, 0, -0.21); ctx.stroke();
  ctx.fillStyle = '#3fa652'; ell(0.025, -0.16, 0.02, 0.009);
  ctx.fillStyle = '#ff2b4e'; circ(0, -0.22, 0.028);
  ctx.fillStyle = '#ff5470'; circ(0.008, -0.225, 0.018);
  ctx.fillStyle = '#ffd166'; circ(0, -0.22, 0.007);
  ctx.fillStyle = 'rgba(210, 240, 255, 0.28)';
  ctx.beginPath();
  ctx.moveTo(-0.05, -0.11); ctx.lineTo(-0.05, -0.24);
  ctx.arc(0, -0.24, 0.05, Math.PI, 0);
  ctx.lineTo(0.05, -0.11); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = 'rgba(235, 250, 255, 0.75)'; ctx.lineWidth = 0.014; ctx.stroke();
  ctx.strokeStyle = 'rgba(255, 255, 255, 0.85)'; ctx.lineWidth = 0.012;
  ctx.beginPath(); ctx.arc(0, -0.24, 0.04, Math.PI * 1.15, Math.PI * 1.55); ctx.stroke();
  ctx.fillStyle = 'rgba(230, 245, 255, 0.9)'; circ(0, -0.3, 0.012);
  ctx.restore();

  // 12. 집 좌측 B-612 푯말
  ctx.save();
  ctx.translate(-0.43, 0);
  ctx.strokeStyle = '#8a5a35'; ctx.lineWidth = 0.022; line(0, 0, 0, -0.18);
  ctx.fillStyle = '#e8d5b5'; ctx.fillRect(-0.08, -0.24, 0.16, 0.08);
  ctx.strokeStyle = '#997350'; ctx.lineWidth = 0.01; ctx.strokeRect(-0.08, -0.24, 0.16, 0.08);
  ctx.font = 'bold 0.045px sans-serif';
  ctx.fillStyle = '#6a472d';
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('B-612', 0, -0.2);
  ctx.restore();
}

function drawBoy(c, t) {
  const run = c.speed > 0.02, sw = run ? Math.sin(c.phase) : 0;
  const bob = run ? Math.abs(Math.cos(c.phase)) * 0.035 : Math.sin(t * 2.2) * 0.008;
  ctx.fillStyle = 'rgba(20,30,40,0.24)'; ell(0, 0, 0.24 * (1 - c.jump * 0.9), 0.055);
  ctx.scale(c.face, 1); ctx.translate(0, -c.jump - bob);
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';

  // 바람에 날리는 목도리
  const fl = Math.sin(t * 7 + c.phase * 0.3) * 0.045, back = run ? 0.16 : 0;
  ctx.strokeStyle = '#ffcf3a'; ctx.lineWidth = 0.075;
  ctx.beginPath(); ctx.moveTo(-0.05, -0.6);
  ctx.bezierCurveTo(-0.2, -0.64 + fl, -0.3 - back, -0.52 - fl - (run ? 0.1 : 0), -0.44 - back, -0.5 + fl + (run ? -0.12 : 0.12));
  ctx.stroke();

  // 다리
  for (const s of [-1, 1]) {
    const a = sw * 0.8 * s, hx = 0.045 * s, hy = -0.3;
    const fx = hx + Math.sin(a) * 0.27, fy = hy + Math.cos(a) * 0.27;
    ctx.strokeStyle = '#f3efe6'; ctx.lineWidth = 0.085; line(hx, hy, fx, fy);
    ctx.fillStyle = '#6b4a2f'; ell(fx + 0.03, fy, 0.065, 0.038);
  }
  const arm = (a) => {
    const ex = Math.sin(a) * 0.2, ey = -0.56 + Math.cos(a) * 0.2;
    ctx.strokeStyle = '#3d9474'; ctx.lineWidth = 0.07; line(0, -0.56, ex, ey);
    ctx.fillStyle = '#ffe2c6'; circ(ex, ey, 0.034);
  };
  arm(run ? -sw * 0.9 : -0.25);
  // 외투
  ctx.fillStyle = '#4fae8a';
  ctx.beginPath(); ctx.moveTo(-0.11, -0.62); ctx.quadraticCurveTo(0, -0.66, 0.11, -0.62);
  ctx.lineTo(0.17, -0.27); ctx.quadraticCurveTo(0, -0.23, -0.17, -0.27); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = '#2f7f66'; ctx.lineWidth = 0.03; line(-0.145, -0.4, 0.145, -0.4);
  ctx.fillStyle = '#ffe9a6'; circ(0.02, -0.4, 0.022);
  arm(run ? sw * 0.9 : 0.25);
  ctx.fillStyle = '#ffcf3a'; ell(0, -0.615, 0.125, 0.05);

  // 머리
  ctx.fillStyle = '#ffe2c6'; circ(0.01, -0.8, 0.18);
  ctx.fillStyle = '#f4b93a';
  ctx.beginPath(); ctx.arc(0.01, -0.8, 0.188, Math.PI * 0.92, Math.PI * 1.93);
  ctx.quadraticCurveTo(0.1, -0.9, 0.02, -0.86); ctx.quadraticCurveTo(-0.08, -0.82, -0.17, -0.74); ctx.closePath(); ctx.fill();
  ctx.beginPath(); ctx.moveTo(-0.08, -0.96); ctx.lineTo(-0.05, -1.05); ctx.lineTo(0, -0.97); ctx.lineTo(0.05, -1.06); ctx.lineTo(0.09, -0.96); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#2b2118'; circ(0.07, -0.79, 0.022); circ(0.15, -0.79, 0.019);
  ctx.fillStyle = 'rgba(255,120,120,0.45)'; ell(0.125, -0.73, 0.036, 0.022);
  ctx.strokeStyle = '#a8543f'; ctx.lineWidth = 0.014;
  ctx.beginPath(); ctx.arc(0.1, -0.735, 0.034, Math.PI * 0.2, Math.PI * 0.8); ctx.stroke();
}

function drawDog(c, t) {
  const run = c.speed > 0.02, sw = run ? Math.sin(c.phase) : 0;
  const bob = run ? Math.abs(Math.cos(c.phase)) * 0.04 : 0;
  ctx.fillStyle = 'rgba(20,30,40,0.22)'; ell(0, 0, 0.36 * (1 - c.jump * 0.8), 0.06);
  ctx.scale(c.face, 1); ctx.translate(0, -c.jump - bob);
  ctx.lineCap = 'round';
  const wag = Math.sin(t * (run ? 16 : 11)) * 0.12;
  ctx.strokeStyle = '#d99a4e'; ctx.lineWidth = 0.075; line(-0.3, -0.44, -0.44 + wag * 0.4, -0.66 + Math.abs(wag) * 0.2);
  const legs = [[-0.22, 1], [-0.14, -1], [0.16, -1], [0.24, 1]];
  for (const [lx, s] of legs) {
    const a = sw * 0.75 * s, fx = lx + Math.sin(a) * 0.26, fy = -0.3 + Math.cos(a) * 0.26;
    ctx.strokeStyle = s > 0 ? '#e0a458' : '#c98c44'; ctx.lineWidth = 0.085; line(lx, -0.3, fx, fy);
    ctx.fillStyle = '#fff6e6'; circ(fx + 0.015, fy, 0.048);
  }
  ctx.fillStyle = '#e0a458'; ell(0, -0.41, 0.33, 0.17);
  ctx.fillStyle = '#fbe9cc'; ell(0.04, -0.33, 0.2, 0.075);
  ctx.strokeStyle = '#e8503a'; ctx.lineWidth = 0.05; line(0.2, -0.5, 0.27, -0.41);
  ctx.fillStyle = '#e0a458'; circ(0.33, -0.62, 0.175);
  ctx.fillStyle = '#fbe9cc'; ell(0.46, -0.57, 0.105, 0.08);
  ctx.fillStyle = '#2b2118'; circ(0.545, -0.6, 0.032); circ(0.37, -0.66, 0.026);
  ctx.fillStyle = '#fff'; circ(0.378, -0.668, 0.009);
  if (run || c.state === 'idle') { ctx.fillStyle = '#ff8fa3'; ell(0.47, -0.495, 0.03, 0.045); }
  ctx.fillStyle = '#a86a32';
  ctx.save(); ctx.translate(0.23, -0.74); ctx.rotate(0.5 + (run ? sw * 0.35 : 0)); ctx.beginPath(); ctx.ellipse(0, 0.1, 0.075, 0.15, 0, 0, TAU); ctx.fill(); ctx.restore();
}

function drawCat(c, t) {
  const run = c.speed > 0.02, sw = run ? Math.sin(c.phase) : 0;
  const bob = run ? Math.abs(Math.cos(c.phase)) * 0.035 : 0;
  ctx.fillStyle = 'rgba(20,30,40,0.22)'; ell(0, 0, 0.32 * (1 - c.jump * 0.8), 0.055);
  ctx.scale(c.face, 1); ctx.translate(0, -c.jump - bob);
  ctx.lineCap = 'round';
  const tw = Math.sin(t * (run ? 6 : 2.4)) * 0.1;
  ctx.strokeStyle = '#7f8aa3'; ctx.lineWidth = 0.065;
  ctx.beginPath(); ctx.moveTo(-0.27, -0.38); ctx.bezierCurveTo(-0.5, -0.4, -0.5 + tw, -0.7, -0.38 + tw * 1.6, -0.86); ctx.stroke();
  const legs = [[-0.2, 1], [-0.13, -1], [0.14, -1], [0.21, 1]];
  for (const [lx, s] of legs) {
    const a = sw * 0.8 * s, fx = lx + Math.sin(a) * 0.22, fy = -0.24 + Math.cos(a) * 0.22;
    ctx.strokeStyle = s > 0 ? '#8f9bb3' : '#7c88a1'; ctx.lineWidth = 0.07; line(lx, -0.24, fx, fy);
    ctx.fillStyle = '#ffffff'; circ(fx + 0.012, fy, 0.04);
  }
  ctx.fillStyle = '#8f9bb3'; ell(0, -0.34, 0.29, 0.14);
  ctx.strokeStyle = '#6f7b94'; ctx.lineWidth = 0.028;
  for (const sx of [-0.12, -0.02, 0.08]) line(sx, -0.47, sx + 0.03, -0.39);
  ctx.fillStyle = '#ffffff'; ell(0.05, -0.27, 0.16, 0.055);
  // 귀 · 머리
  ctx.fillStyle = '#8f9bb3';
  ctx.beginPath(); ctx.moveTo(0.15, -0.6); ctx.lineTo(0.17, -0.78); ctx.lineTo(0.27, -0.66); ctx.closePath(); ctx.fill();
  ctx.beginPath(); ctx.moveTo(0.29, -0.66); ctx.lineTo(0.39, -0.78); ctx.lineTo(0.42, -0.6); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#ffb3c1';
  ctx.beginPath(); ctx.moveTo(0.33, -0.66); ctx.lineTo(0.385, -0.73); ctx.lineTo(0.4, -0.63); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#8f9bb3'; circ(0.29, -0.52, 0.155);
  ctx.fillStyle = '#ffffff'; ell(0.36, -0.47, 0.085, 0.06);
  const blink = frac(t * 0.27 + 0.3) < 0.04;
  ctx.fillStyle = '#2b2118';
  if (blink) { ctx.fillRect(0.27, -0.545, 0.05, 0.01); ctx.fillRect(0.37, -0.545, 0.045, 0.01); }
  else { ctx.fillStyle = '#7bd389'; ell(0.295, -0.54, 0.026, 0.03); ell(0.39, -0.54, 0.023, 0.028); ctx.fillStyle = '#1d1a14'; ell(0.3, -0.54, 0.01, 0.024); ell(0.394, -0.54, 0.009, 0.022); }
  ctx.fillStyle = '#ff8fa3'; ell(0.405, -0.49, 0.016, 0.012);
  ctx.strokeStyle = 'rgba(255,255,255,0.9)'; ctx.lineWidth = 0.008;
  line(0.42, -0.475, 0.56, -0.5); line(0.42, -0.465, 0.56, -0.455); line(0.3, -0.47, 0.18, -0.49);
}

function drawGlobeScene(t, dt) {
  const R = view.R, cx = view.cx, cy = view.cy + Math.sin(t * 0.8) * R * 0.02;

  // 그림자와 대기 빛
  ctx.fillStyle = 'rgba(12,30,60,0.2)';
  ctx.save(); ctx.translate(cx, cy + R * 1.34); ctx.scale(1, 0.16);
  const sg = ctx.createRadialGradient(0, 0, 0, 0, 0, R * 1.05);
  sg.addColorStop(0, 'rgba(10,25,55,0.42)'); sg.addColorStop(1, 'rgba(10,25,55,0)');
  ctx.fillStyle = sg; ctx.beginPath(); ctx.arc(0, 0, R * 1.05, 0, TAU); ctx.fill(); ctx.restore();
  const ag = ctx.createRadialGradient(cx, cy, R * 0.9, cx, cy, R * 1.28);
  ag.addColorStop(0, 'rgba(150,210,255,0.5)'); ag.addColorStop(0.35, 'rgba(160,210,255,0.2)'); ag.addColorStop(1, 'rgba(160,210,255,0)');
  ctx.fillStyle = ag; ctx.beginPath(); ctx.arc(cx, cy, R * 1.28, 0, TAU); ctx.fill();

  // 그릴 것 모으기
  const items = [];
  const add = (p, size, fn, obj) => {
    const v = mulMV(M, p);
    if (v[2] < -0.5) return;
    items.push({ v, size, fn, obj });
  };
  for (const f of flowers) add(f.p, R * 0.085 * f.s, drawFlower, f);
  for (const tr of trees) add(tr.p, R * 0.3 * tr.s, drawTree, tr);
  add(house.p, R * 0.45, drawHouse, house);
  add(cat.p, R * 0.3, drawCat, cat);
  add(dog.p, R * 0.33, drawDog, dog);
  add(boy.p, R * 0.4, drawBoy, boy);
  items.sort((a, b) => a.v[2] - b.v[2]);

  const drawItem = (it) => {
    const v = it.v;
    let ux = v[0], uy = v[1] + 0.6 * Math.max(0, v[2]);
    const l = Math.hypot(ux, uy);
    if (l < 0.06) { ux = 0; uy = 1; } else { ux /= l; uy /= l; }
    const s = it.size * (0.88 + 0.12 * v[2]);
    ctx.save();
    ctx.translate(cx + v[0] * R, cy - v[1] * R);
    ctx.rotate(Math.atan2(ux, uy));
    ctx.scale(s, s);
    it.fn(it.obj, t);
    ctx.restore();
  };

  for (const it of items) if (it.v[2] < 0) drawItem(it);          // 지구 뒤편에서 살짝 보이는 것들
  renderGlobe(M, Math.floor(t * 4) % TW);
  ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = 'high';
  ctx.drawImage(gbuf, cx - R, cy - R, R * 2, R * 2);
  for (const it of items) if (it.v[2] >= 0) drawItem(it);
}

function worldUpdate(dt, t) {
  boyUpdate(dt, t);
  animalUpdate(dog, dt);
  animalUpdate(cat, dt);
  // 집 주변을 지나갈 때 부드럽게 돌아가도록 거리 유지
  for (const c of [boy, dog, cat]) {
    const gap = angleBetween(c.p, house.p);
    if (gap < 0.16) {
      const k = dot(c.p, house.p);
      let away = [c.p[0] - k * house.p[0], c.p[1] - k * house.p[1], c.p[2] - k * house.p[2]];
      if (Math.hypot(away[0], away[1], away[2]) < 1e-4) away = c.h;
      away = norm(away);
      const push = (0.16 - gap) * Math.min(1, dt * 5);
      c.p = norm([c.p[0] + away[0] * push, c.p[1] + away[1] * push, c.p[2] + away[2] * push]);
      const d = dot(c.h, c.p);
      c.h = norm([c.h[0] - d * c.p[0], c.h[1] - d * c.p[1], c.h[2] - d * c.p[2]]);
    }
  }
  for (const c of [boy, dog, cat]) {
    const hv = mulMV(M, c.h);
    if (c.speed > 0.02 && Math.abs(hv[0]) > 0.18) c.face = hv[0] > 0 ? 1 : -1;
  }
  // 카메라가 아이를 부드럽게 따라간다 → 지구가 굴러가는 것처럼 보인다
  const vB = mulMV(M, boy.p), ang = angleBetween(vB, BOY_VIEW);
  if (ang > 1e-4) {
    const ax = cross(vB, BOY_VIEW), l = Math.hypot(ax[0], ax[1], ax[2]);
    if (l > 1e-6) M = orthonormalize(mulMM(rotAxis([ax[0] / l, ax[1] / l, ax[2] / l], ang * (1 - Math.exp(-dt * 2.4))), M));
  }
}

/* =========================================================
   파도 소리 (Web Audio 로 직접 합성 · 화면의 파도와 박자를 맞춤)
   ========================================================= */
let actx = null, master = null, washG, washF, hissG, rumbleG, soundOn = false;
const btnSound = document.getElementById('btnSound');

function pinkNoise(data) {
  let b0 = 0, b1 = 0, b2 = 0, b3 = 0, b4 = 0, b5 = 0, b6 = 0;
  for (let i = 0; i < data.length; i++) {
    const w = Math.random() * 2 - 1;
    b0 = 0.99886 * b0 + w * 0.0555179; b1 = 0.99332 * b1 + w * 0.0750759; b2 = 0.969 * b2 + w * 0.153852;
    b3 = 0.8665 * b3 + w * 0.3104856; b4 = 0.55 * b4 + w * 0.5329522; b5 = -0.7616 * b5 - w * 0.016898;
    data[i] = (b0 + b1 + b2 + b3 + b4 + b5 + b6 + w * 0.5362) * 0.11; b6 = w * 0.115926;
  }
}
function initAudio() {
  const AC = window.AudioContext || window.webkitAudioContext;
  if (!AC) return false;
  actx = new AC();
  const buf = actx.createBuffer(2, actx.sampleRate * 7, actx.sampleRate);
  pinkNoise(buf.getChannelData(0)); pinkNoise(buf.getChannelData(1));
  const src = actx.createBufferSource(); src.buffer = buf; src.loop = true;

  master = actx.createGain(); master.gain.value = 0; master.connect(actx.destination);

  const rumbleF = actx.createBiquadFilter(); rumbleF.type = 'lowpass'; rumbleF.frequency.value = 190;
  rumbleG = actx.createGain(); rumbleG.gain.value = 0.3;
  src.connect(rumbleF); rumbleF.connect(rumbleG); rumbleG.connect(master);

  washF = actx.createBiquadFilter(); washF.type = 'lowpass'; washF.frequency.value = 500; washF.Q.value = 0.4;
  washG = actx.createGain(); washG.gain.value = 0.05;
  src.connect(washF); washF.connect(washG); washG.connect(master);

  const hissF = actx.createBiquadFilter(); hissF.type = 'bandpass'; hissF.frequency.value = 4200; hissF.Q.value = 0.5;
  hissG = actx.createGain(); hissG.gain.value = 0;
  src.connect(hissF); hissF.connect(hissG); hissG.connect(master);

  src.start();
  return true;
}
function setSound(on) {
  if (on && !actx && !initAudio()) { toast('이 브라우저에서는 소리를 낼 수 없어요.'); return; }
  soundOn = on;
  if (actx) {
    if (on) actx.resume();
    master.gain.cancelScheduledValues(actx.currentTime);
    master.gain.setTargetAtTime(on ? 0.75 : 0, actx.currentTime, on ? 0.8 : 0.25);
  }
  btnSound.setAttribute('aria-pressed', String(on));
  btnSound.textContent = on ? '♪ 파도 소리 켜짐' : '♪ 파도 소리 켜기';
}
function updateAudio(u, t) {
  if (!actx || !soundOn) return;
  const now = actx.currentTime;
  // 부서지며 밀려오는 '쏴아' → 모래를 훑고 빠지는 '스르르'
  const rush = u < 0.13 ? Math.pow(u / 0.13, 1.5) : Math.exp(-(u - 0.13) * 3.6);
  const build = smooth(0.7, 1, u);
  const back = Math.sin(Math.PI * clamp((u - 0.26) / 0.62, 0, 1));
  washG.gain.setTargetAtTime(0.05 + 0.6 * rush + 0.1 * build, now, 0.09);
  washF.frequency.setTargetAtTime(420 + 2500 * rush + 250 * build, now, 0.09);
  hissG.gain.setTargetAtTime(0.02 + 0.2 * back + 0.16 * rush, now, 0.12);
  rumbleG.gain.setTargetAtTime(0.26 + 0.1 * Math.sin(t * 0.41) + 0.3 * build + 0.15 * rush, now, 0.15);
}
btnSound.addEventListener('click', (e) => { e.stopPropagation(); autoStarted = true; setSound(!soundOn); });
let autoStarted = false;
function firstGesture() {
  if (autoStarted) return;
  autoStarted = true;
  setSound(true);
}
window.addEventListener('pointerdown', firstGesture, { once: false });
window.addEventListener('keydown', firstGesture);
document.addEventListener('visibilitychange', () => {
  if (!actx) return;
  if (document.hidden) actx.suspend(); else if (soundOn) actx.resume();
});

/* =========================================================
   조작 (방향키 · 터치 버튼 · AI 모드)
   ========================================================= */
const btnMode = document.getElementById('btnMode');
const isTyping = (el) => el && (el.tagName === 'INPUT' || el.tagName === 'TEXTAREA');
window.addEventListener('keydown', (e) => {
  if (e.key === 'Escape') { if (!lightbox.hidden) lightbox.hidden = true; else if (panelOpen) closePanel(); return; }
  if (isTyping(e.target)) return;
  if (e.key.startsWith('Arrow')) { keys.add(e.key); e.preventDefault(); }
  else if (e.key === ' ' && e.target.tagName !== 'BUTTON') { hop(boy, 2); e.preventDefault(); }
});
window.addEventListener('keyup', (e) => keys.delete(e.key));
window.addEventListener('blur', () => keys.clear());
btnMode.addEventListener('click', () => {
  aiMode = !aiMode; lastInput = -99;
  btnMode.setAttribute('aria-pressed', String(aiMode));
  btnMode.textContent = aiMode ? 'AI 모드' : '직접 조종';
});
document.querySelectorAll('.dpad button').forEach((b) => {
  const k = b.dataset.key;
  const down = (e) => { e.preventDefault(); if (k === 'Jump') hop(boy, 2); else keys.add(k); };
  const up = () => keys.delete(k);
  b.addEventListener('pointerdown', down);
  b.addEventListener('pointerup', up); b.addEventListener('pointerleave', up); b.addEventListener('pointercancel', up);
});

/* =========================================================
   게시판 · 방명록 (브라우저 저장소 사용)
   ========================================================= */
const K_POSTS = 'dawnPlanet.posts.v1', K_GUEST = 'dawnPlanet.guest.v1';
const $ = (id) => document.getElementById(id);
const lightbox = $('lightbox');
const toastEl = $('toast');
let toastTimer = 0;
function toast(msg) {
  toastEl.textContent = msg; toastEl.classList.add('show');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => toastEl.classList.remove('show'), 2600);
}
function load(key, seed) {
  try { const v = JSON.parse(localStorage.getItem(key)); if (Array.isArray(v)) return v; } catch (e) { /* 저장소를 못 쓰면 기본값 */ }
  return seed;
}
function save(key, value) {
  try { localStorage.setItem(key, JSON.stringify(value)); return true; }
  catch (e) { return false; }
}
// 삭제는 두 번 눌러야 실행된다 (첫 번째는 확인 요청, 3초 뒤 원래대로)
function armDelete(btn) {
  if (btn.dataset.armed) return true;
  const old = btn.textContent;
  btn.dataset.armed = '1'; btn.textContent = '한 번 더 누르면 삭제';
  setTimeout(() => { delete btn.dataset.armed; btn.textContent = old; }, 3000);
  return false;
}
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
const pad = (n) => String(n).padStart(2, '0');
function fmtDate(ms) {
  const d = new Date(ms);
  return `${d.getFullYear()}.${pad(d.getMonth() + 1)}.${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}`;
}
function el(tag, props, ...kids) {
  const n = document.createElement(tag);
  if (props) for (const k in props) { if (k === 'class') n.className = props[k]; else if (k === 'text') n.textContent = props[k]; else if (k.startsWith('on')) n.addEventListener(k.slice(2), props[k]); else n.setAttribute(k, props[k]); }
  for (const k of kids) if (k) n.append(k);
  return n;
}

const SEED_POSTS = [{
  id: 'welcome', author: '별지기', title: '작은 별에 오신 걸 환영해요', date: Date.now(),
  body: '해가 떠오르는 바다 앞, 작은 지구에 놀러 오셨네요.\n\n방향키로 아이를 직접 움직여 볼 수 있어요. 강아지와 고양이는 알아서 따라다니며 놀아요.\n\n글쓰기 버튼을 눌러 사진과 함께 이야기를 남겨 보세요.', photo: null,
}];
const SEED_GUESTS = [{ id: 'hello', author: '별지기', date: Date.now(), body: '파도 소리 들으며 편히 쉬다 가세요.', photo: null }];

// 저장 방식: 공유 페이지에서는 모두가 함께 보는 공용 저장소, 내 컴퓨터에서 파일로 열면 이 브라우저
const hosted = !!(window.claude && typeof window.claude.use === 'function');
let mode = hosted ? 'loading' : 'local';      // loading | shared | local | failed
let posts = hosted ? [] : load(K_POSTS, SEED_POSTS);
let guests = hosted ? [] : load(K_GUEST, SEED_GUESTS);
let sdb = null, myId = null, amOwner = false, canWrite = true, slow = false;

const canRemove = (e) => mode === 'local' || (mode === 'shared' && canWrite && (amOwner || (!!myId && e.authorId === myId)));
const safePhoto = (p) => (typeof p === 'string' && p.startsWith('data:image/') ? p : null);

function updateNote() {
  let t;
  if (mode === 'loading') t = slow ? '아직 글을 불러오지 못했어요. 연결을 기다리는 중이에요.' : '글을 불러오는 중이에요…';
  else if (mode === 'failed') t = '지금은 글을 불러올 수 없어요.';
  else if (mode === 'local') t = '여기 남긴 글은 이 브라우저에만 저장돼요.';
  else if (!canWrite) t = '읽기 전용으로 보고 있어요. 글을 남기려면 주인에게 참여 권한을 요청하세요.';
  else t = slow ? '연결이 느려 최신 글이 아닐 수 있어요.' : '모두가 함께 보는 공간이에요. 남긴 글은 다른 방문자에게도 보여요.';
  $('storeNote').textContent = t;
  const readOnly = mode === 'loading' || mode === 'failed' || (mode === 'shared' && !canWrite);
  $('btnWrite').hidden = readOnly; $('guestForm').hidden = readOnly;
}

async function saveEntry(col, entry) {
  if (mode === 'shared') {
    const body = { ...entry }; delete body.id;
    if (myId) body.authorId = myId;
    await sdb.collection(col).doc(entry.id).set(body);
    return;
  }
  const next = [entry, ...(col === 'posts' ? posts : guests)];
  if (!save(col === 'posts' ? K_POSTS : K_GUEST, next)) throw { code: 'local_full' };
  if (col === 'posts') posts = next; else guests = next;
}
async function removeEntry(col, id) {
  if (mode === 'shared') { await sdb.collection(col).doc(id).delete(); return; }
  if (col === 'posts') { posts = posts.filter((x) => x.id !== id); save(K_POSTS, posts); }
  else { guests = guests.filter((x) => x.id !== id); save(K_GUEST, guests); }
}
function writeError(e) {
  const c = e && e.code;
  if (c === 'local_full' || c === 'quota_exceeded') toast('저장 공간이 가득 찼어요. 사진을 빼거나 오래된 글을 지워 주세요.');
  else if (c === 'invalid_argument' || c === 'revoked' || c === 'not_granted') {
    canWrite = false; updateNote(); renderPosts(); renderGuests(); showBoard('list');
    toast('글을 남길 권한이 없어요.');
  } else toast('저장하지 못했어요. 잠시 뒤 다시 시도해 주세요.');
}

async function connectShared() {
  let db = null, user = null;
  try { db = await window.claude.use('db'); user = await window.claude.use('user'); } catch (e) { /* 없으면 이 브라우저에 저장 */ }
  if (!db) {
    mode = 'local'; posts = load(K_POSTS, SEED_POSTS); guests = load(K_GUEST, SEED_GUESTS);
    updateNote(); renderPosts(); renderGuests(); return;
  }
  sdb = db;
  if (user) {
    try {
      myId = await user.id();
      amOwner = !!(await user.isOwner());
      if ((await user.can('data.write')) === false) canWrite = false;
    } catch (e) { /* 알 수 없으면 입력을 열어 두고, 거절되면 읽기 전용으로 바꾼다 */ }
  }
  const timer = setTimeout(() => { slow = true; updateNote(); }, 10000);
  let dead = false;
  const watch = (col, apply) => db.collection(col).orderBy('date', 'desc').limit(200).onSnapshot((snap) => {
    if (dead) return;
    if (mode === 'loading') mode = 'shared';
    if (!snap.metadata.fromCache) { clearTimeout(timer); slow = false; }
    apply(snap.docs.map((d) => ({ ...d.data(), id: d.id })));
    updateNote();
  }, () => { dead = true; clearTimeout(timer); mode = 'failed'; updateNote(); renderPosts(); renderGuests(); });
  watch('posts', (v) => { posts = v; renderPosts(); });
  watch('guestbook', (v) => { guests = v; renderGuests(); });
}

// 사진: 저장 공간을 아끼려고 줄여서 보관
function readImage(file) {
  return new Promise((resolve, reject) => {
    if (!file) return resolve(null);
    if (!file.type.startsWith('image/')) return reject(new Error('사진 파일만 올릴 수 있어요.'));
    const url = URL.createObjectURL(file), img = new Image();
    img.onload = () => {
      // 글 하나에 담을 수 있는 크기 안으로 들어올 때까지 줄인다
      let out = '';
      for (const [side, q] of [[900, 0.8], [760, 0.72], [620, 0.66], [480, 0.6], [360, 0.55]]) {
        const k = Math.min(1, side / Math.max(img.width, img.height));
        const c = document.createElement('canvas');
        c.width = Math.max(1, Math.round(img.width * k)); c.height = Math.max(1, Math.round(img.height * k));
        const g = c.getContext('2d'); g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height); g.drawImage(img, 0, 0, c.width, c.height);
        out = c.toDataURL('image/jpeg', q);
        if (out.length <= 200000) break;
      }
      URL.revokeObjectURL(url);
      if (out.length > 200000) return reject(new Error('사진이 너무 커요. 다른 사진을 골라 주세요.'));
      resolve(out);
    };
    img.onerror = () => { URL.revokeObjectURL(url); reject(new Error('이 사진은 열 수 없어요. 다른 사진을 골라 주세요.')); };
    img.src = url;
  });
}
function wirePhoto(form) {
  const input = form.querySelector('input[type=file]'), box = form.querySelector('.preview');
  const img = box.querySelector('img'), nameEl = form.querySelector('.file-name');
  const state = { data: null };
  const clear = () => { state.data = null; input.value = ''; box.hidden = true; img.removeAttribute('src'); if (nameEl) nameEl.textContent = '선택한 사진 없음'; };
  input.addEventListener('change', async () => {
    const f = input.files[0];
    if (!f) return clear();
    try { state.data = await readImage(f); img.src = state.data; box.hidden = false; if (nameEl) nameEl.textContent = f.name; }
    catch (err) { clear(); toast(err.message); }
  });
  box.querySelector('.remove').addEventListener('click', clear);
  state.clear = clear;
  return state;
}
const openPhoto = (src) => { lightbox.querySelector('img').src = src; lightbox.hidden = false; };
lightbox.addEventListener('click', () => { lightbox.hidden = true; });

// ----- 게시판 -----
const boardList = $('boardList'), boardDetail = $('boardDetail'), boardForm = $('boardForm');
const boardPhoto = wirePhoto(boardForm);
function showBoard(mode) {
  boardList.hidden = mode !== 'list'; boardDetail.hidden = mode !== 'detail'; boardForm.hidden = mode !== 'write';
  document.querySelector('.panel-body').scrollTop = 0;
}
function renderPosts() {
  const ul = $('postList'); ul.replaceChildren();
  $('boardCount').textContent = `전체 ${posts.length}개`;
  if (!posts.length) ul.append(el('li', { class: 'empty-note', text: mode === 'loading' ? '글을 불러오는 중이에요…' : mode === 'failed' ? '지금은 글을 불러올 수 없어요.' : '아직 글이 없어요. 글쓰기를 눌러 첫 글을 남겨 보세요.' }));
  for (const p of posts) {
    const photo = safePhoto(p.photo);
    const thumb = photo ? el('img', { class: 'thumb', src: photo, alt: '' }) : el('div', { class: 'thumb empty', text: String(p.title || '글').slice(0, 1) });
    ul.append(el('li', { tabindex: '0', onclick: () => openPost(p.id), onkeydown: (e) => { if (e.key === 'Enter') openPost(p.id); } },
      thumb,
      el('div', { class: 'info' }, el('div', { class: 'title', text: p.title }), el('div', { class: 'meta', text: `${p.author} · ${fmtDate(p.date)}${photo ? ' · 사진' : ''}` }))));
  }
}
function openPost(id) {
  const p = posts.find((x) => x.id === id); if (!p) return;
  const photo = safePhoto(p.photo);
  boardDetail.className = 'detail';
  boardDetail.replaceChildren(
    el('h2', { text: p.title }),
    el('div', { class: 'meta', text: `${p.author} · ${fmtDate(p.date)}` }),
    photo ? el('img', { class: 'photo', src: photo, alt: '올린 사진', onclick: () => openPhoto(photo) }) : null,
    el('div', { class: 'body', text: p.body }),
    el('div', { class: 'form-actions' },
      canRemove(p) ? el('button', { type: 'button', class: 'btn danger', text: '삭제', onclick: async (e) => {
        if (!armDelete(e.currentTarget)) return;
        try { await removeEntry('posts', id); renderPosts(); showBoard('list'); toast('글을 지웠어요.'); }
        catch (err) { writeError(err); }
      } }) : el('span'),
      el('button', { type: 'button', class: 'btn', text: '목록으로', onclick: () => showBoard('list') })));
  showBoard('detail');
}
$('btnWrite').addEventListener('click', () => { showBoard('write'); boardForm.elements.author.focus(); });
$('btnCancel').addEventListener('click', () => { boardForm.reset(); boardPhoto.clear(); showBoard('list'); });
boardForm.addEventListener('submit', async (e) => {
  e.preventDefault();
  const f = boardForm.elements, btn = boardForm.querySelector('[type=submit]');
  const post = { id: uid(), author: f.author.value.trim(), title: f.title.value.trim(), body: f.body.value.trim(), photo: boardPhoto.data, date: Date.now() };
  if (!post.author || !post.title || !post.body) return toast('이름, 제목, 내용을 모두 적어 주세요.');
  btn.disabled = true;
  try { await saveEntry('posts', post); boardForm.reset(); boardPhoto.clear(); renderPosts(); showBoard('list'); toast('글을 올렸어요.'); }
  catch (err) { writeError(err); }
  finally { btn.disabled = false; }
});

// ----- 방명록 -----
const guestForm = $('guestForm'), guestPhoto = wirePhoto(guestForm);
const AVATARS = ['#ee7355', '#f6a04d', '#4fae8a', '#5b8def', '#b388eb', '#e86a92'];
function renderGuests() {
  const ul = $('guestList'); ul.replaceChildren();
  $('guestCount').textContent = `${guests.length}명이 다녀갔어요`;
  if (!guests.length) ul.append(el('li', { class: 'empty-note', text: mode === 'loading' ? '방명록을 불러오는 중이에요…' : mode === 'failed' ? '지금은 방명록을 불러올 수 없어요.' : '아직 다녀간 흔적이 없어요. 첫 인사를 남겨 보세요.' }));
  for (const g of guests) {
    const author = String(g.author || '손님'), photo = safePhoto(g.photo);
    let hsum = 0; for (const ch of author) hsum += ch.codePointAt(0);
    const av = el('div', { class: 'avatar', text: author.slice(0, 1) }); av.style.background = AVATARS[hsum % AVATARS.length];
    ul.append(el('li', null, av,
      el('div', { class: 'content' },
        el('div', { class: 'who' }, el('b', { text: author }), el('time', { text: fmtDate(g.date) }),
          canRemove(g) ? el('button', { type: 'button', text: '삭제', 'aria-label': `${author} 님의 글 삭제`, onclick: async (e) => {
            if (!armDelete(e.currentTarget)) return;
            try { await removeEntry('guestbook', g.id); renderGuests(); }
            catch (err) { writeError(err); }
          } }) : null),
        el('p', { text: g.body }),
        photo ? el('img', { src: photo, alt: '올린 사진', onclick: () => openPhoto(photo) }) : null)));
  }
}
guestForm.addEventListener('submit', async (e) => {
  e.preventDefault();
  const f = guestForm.elements, btn = guestForm.querySelector('[type=submit]');
  const g = { id: uid(), author: f.author.value.trim(), body: f.body.value.trim(), photo: guestPhoto.data, date: Date.now() };
  if (!g.author || !g.body) return toast('이름과 내용을 적어 주세요.');
  btn.disabled = true;
  try { await saveEntry('guestbook', g); guestForm.reset(); guestPhoto.clear(); renderGuests(); toast('방명록을 남겼어요.'); }
  catch (err) { writeError(err); }
  finally { btn.disabled = false; }
});

// ----- 패널 · 탭 -----
function selectTab(name) {
  document.querySelectorAll('.tabs button').forEach((b) => b.setAttribute('aria-selected', String(b.dataset.tab === name)));
  $('tab-board').hidden = name !== 'board'; $('tab-guest').hidden = name !== 'guest';
  document.querySelector('.panel-body').scrollTop = 0;
}
function openPanel(name) {
  panelOpen = true; document.body.classList.add('panel-open'); panel.setAttribute('aria-hidden', 'false');
  selectTab(name); if (name === 'board') showBoard('list');
  computeTarget();
}
function closePanel() {
  panelOpen = false; document.body.classList.remove('panel-open'); panel.setAttribute('aria-hidden', 'true');
  if (panel.contains(document.activeElement)) document.activeElement.blur();
  computeTarget();
}
document.querySelectorAll('.side-menu button').forEach((b) => b.addEventListener('click', () => openPanel(b.dataset.open)));
document.querySelectorAll('.tabs button').forEach((b) => b.addEventListener('click', () => selectTab(b.dataset.tab)));
$('btnClose').addEventListener('click', closePanel);

/* =========================================================
   시작
   ========================================================= */
buildTextures();
plant();
resize();
makeSandPattern();
updateNote(); renderPosts(); renderGuests();
if (hosted) connectShared();
window.addEventListener('resize', resize);

let last = 0, simT = 0;
function frame(ms) {
  const now = ms / 1000;
  const dt = Math.min(0.05, Math.max(0, now - last)); last = now; simT += dt;
  const k = 1 - Math.exp(-dt * 4.2);
  view.cx = lerp(view.cx, view.tx, k); view.cy = lerp(view.cy, view.ty, k); view.R = lerp(view.R, view.tR, k);

  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const sun = drawSky(simT);
  const u = drawSea(simT, dt, sun);
  worldUpdate(dt, simT);
  drawGlobeScene(simT, dt);
  updateAudio(u, simT);
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);

// 점검용 (콘솔에서 상태 확인)
window.__dawn = { get state() { return { view: { ...view }, panelOpen, aiMode, soundOn, boy: boy.p, posts: posts.length, guests: guests.length }; } };
})();
