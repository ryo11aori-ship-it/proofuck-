import sys,itertools as I;bf={'>':'1','<':'2','+':'3','-':'4','.':'5',',':'6','[':'7',']':'8'};src=open(sys.argv[1]).read() if len(sys.argv)>1 else "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.";tgt="".join(bf.get(c,"") for c in src) or "9";chk=[tgt[max(0,i-5):i] for i in range(len(tgt),0,-5)][::-1];u=set();p=lambda n:n>1 and all(n%i!=0 for i in range(2,int(n**0.5)+1))
def gen_p():
    n=100
    while True:
        if p(n) and n not in u: yield n
        n+=1
P_ITER = gen_p()
def fxy(v):
    while True:
        y = next(P_ITER)
        u.add(y)
        for x in range(max(2,v*y), v*y+y):
            if p(x) and x not in u:
                u.add(x)
                return (x,y)
pass;vg=(v+"'"*i for i in I.count() for v in ['x','y','z']+[chr(j) for j in range(945,970) if j!=962]+[chr(j) for j in range(97,120)]);xt,yt=(fxy(100000) if len(chk)>1 else (0,0));xnt,ynt=(next(vg),next(vg)) if len(chk)>1 else ("","");df=[f"{xnt}={xt}",f"{ynt}={yt}"] if len(chk)>1 else [];tb=f"({xnt}÷{ynt})(6!1)" if len(chk)>1 else "";bks=[];[bks.append((lambda xy,n: (df.extend([f"{n[0]}={xy[0]}",f"{n[1]}={xy[1]}"]), f"({n[0]}÷{n[1]})({len(c)}!1)")[1])(fxy(int(c)), (next(vg),next(vg)))) for c in chk];eq="+\n".join(bks[i]+"".join("×"+tb for _ in range(len(chk)-1-i)) for i in range(len(chk)));sys.stdout.write("∵\n"+"\n".join(df)+f"\n{eq}\n={tgt}\nQ.E.D.\n")
