const {chromium}=require('playwright');
(async()=>{const b=await chromium.launch();const p=await b.newPage({viewport:{width:1080,height:1920}});
await p.goto('file://'+process.cwd()+'/slides.html');await p.waitForTimeout(500);
for(let i=1;i<=4;i++){const el=await p.$('#s'+i);await el.screenshot({path:`slide${i}.png`});
 console.log(i, await p.evaluate(n=>{const e=document.getElementById('s'+n);return [e.scrollHeight,e.clientHeight]},i));}
await b.close()})()
