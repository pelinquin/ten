#!/usr/bin/python3
# -*- coding: utf-8 -*-
""" 
  **** DECENTRALIZED ENHANCED SIGNATURE ****
_________________________________________________________________
 Use the 'desig' iOS app to test on a real device
DEPENDENCIES: ecc.py
USAGE: 
 './desig.py Alice' -> run Alice's phone   
 './desig.py BoB'   -> run Bob's   phone
Each node -> (UDP socket + HTTP server) on same port
Matrix:
   Element16(10:6) src5|dst5 : cumul_val4|last_date2
   Element9 (5:4)  src5      : cumul_tax4
COMMANDS:
 Alice(40)>bob100 -> Alice, with balance 40, pays 100 to Bob
          >i      -> Initialize ports 
          >b      -> Display the current balance
          >c      -> Check balances
          >h      -> Help
RMQS:
 Tax is constant assuming uniform distribution
 Externalities not managed
 Registration process not managed
__________________________________________________________________
CONTACT: laurent.fournier@adox.io (https://adox.io)
"""

import socket, threading, ecc, re, dbm, http.server, socketserver, urllib, fractions, pexpect, requests
MAXP = 10          # Max nb phones
HOST = '127.0.0.1' # local host 
BASP = 5000        # Base port number
SLEN = 96          # Signature length
MLEN = 16          # Message length
STAX = 20          # Solidarity Tax
MAXB = 1000        # SelfDebt limit
BPRT = 6000        # Backend port
class node:
    def __init__(s, name):
        s.n, s.tbl, s.rvs, s.tid, s.tpk, s.pk, me = name, {}, {}, {}, {}, b'', ''
        s.reset()
        threading.Thread(target=s.server).start()
        try:    requests.get('http://%s:%s'% (HOST, BPRT)).content.decode('utf-8')
        except: threading.Thread(target=s.register).start()
        while True:
            c = input('%s(%d)>' % (s.n, s.bal(s.n)))
            if   re.match('^\s*(I|INIT)\s*$',                      c, re.I):  print(s.init())
            elif re.match('^\s*(H|M|HELP|DOC|MAN)\s*$',            c, re.I):  print (__doc__)
            elif re.match('^\s*(B|BAL|BALANCE)\s*$',               c, re.I):  print(s.bal(s.n))
            elif re.match('^\s*(C|CHECK)\s*$',                     c, re.I):  print(s.check())
            elif reg(re.match('^\s*([A-Z]{3,15})\s*(\d{1,4})\s*$', c, re.I)): s.commit(reg)
            else: print('Command not found')

    def init(s):
        t = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        for x in range(MAXP): t.sendto(b'?', (HOST, BASP+x))
        t.settimeout(1)
        while True:
            try:
                m, a = t.recvfrom(1024)
                name = m[48:].decode('utf-8')
                s.tbl[name], s.tid[name], s.tpk[m[:5]], s.rvs[m[:5]] = a[1], m[:5], m[5:48], name
            except: break
        t.settimeout(None)
        s.savepks()
        threading.Thread(target=s.http, args=(s,)).start()
        return s.tbl

    def commit(s, r):
        t, k = socket.socket(socket.AF_INET, socket.SOCK_DGRAM), ecc.ecdsa()
        rcp, val, k.privkey = r.v.group(1).upper(), int(r.v.group(2)), s.getsk() 
        assert rcp in s.tid and s.n != rcp
        msg = s.tid[s.n] + s.tid[rcp] + ecc.i2b(val, 3) + ecc.z1 + s.pos(s.tid[s.n] + s.tid[rcp]) 
        s.add(msg) # add src
        msg += s.sta()
        sgn = k.sign(msg)
        t.sendto(msg + sgn, (HOST, s.tbl[rcp]))
        s.update(t.recvfrom(1024)[0])

    def add(s, m): 
        x, r, d, p, v = m[:10], m[:5], m[5:10], ecc.b2i(m[14:16]), ecc.b2i(m[10:13])
        print ('%s pays %d to %s' % (s.rvs[r], v, s.rvs[d])) 
        with dbm.open(s.n, 'c') as b:
            assert x not in b and p == 0            
            w = ecc.b2i(b[x][:4]) if (x in b and p == ecc.b2i(b[x][4:])) else 0
            y = ecc.b2i(b[r]) if r in b else 0
            t = v*STAX//100
            b[x] = ecc.i2b(w + (v - t), 4) + ecc.i2b(1 + p, 2)
            if r == s.tid[s.n]: b[r] = ecc.i2b(y + t , 4)
            
    def bal(s, w):
        if len(s.tid) < 1: return 0
        t, l = fractions.Fraction(0), len(s.tid)
        with dbm.open(s.n) as b:
            for x in [y for y in b.keys() if len(y) == 10 and len(b[y]) == 6]:
                if   s.tid[w] == x[:5]: t -= ecc.b2i(b[x][:4])
                elif s.tid[w] == x[5:]: t += ecc.b2i(b[x][:4])
            if s.tid[w] in b: t -= ecc.b2i(b[s.tid[w]])
            for x in [y for y in b.keys() if len(y) == 5 and len(b[y]) == 4]:
                t += fractions.Fraction(ecc.b2i(b[x]), l)
            return t
        
    def check(s):
        for x in s.tid:
            b = s.bal(x)
            assert b > - MAXB and b < MAXB
        return {x:s.bal(x).__round__() for x in s.tid}
            
    def sta(s):
        with dbm.open(s.n) as b:
            z = [y for y in b.keys() if len(y) == 5  and len(b[y]) == 4]
            g = [y for y in b.keys() if len(y) == 10 and len(b[y]) == 6]
            l = ecc.i2b(len(z), 2) + ecc.i2b(len(g), 2)
            return l + b''.join([x + b[x] for x in z]) + b''.join([x + b[x] for x in g])

    def update(s, m):
        lz, lg = ecc.b2i(m[:2]), ecc.b2i(m[2:4])
        #print (lz, lg)
        assert len(m) == 4 + lz*9 + lg*16
        z, g = m[4:4+lz*9], m[4+lz*9:]
        t = {x[:5]:ecc.b2i(x[5:]) for x in [z[i:i+9]  for i in range(0,len(z),9)]}
        u = {x[:10]:(x[10:], ecc.b2i(x[10:14]), ecc.b2i(x[14:])) for x in [g[i:i+16] for i in range(0,len(g),16)]}
        with dbm.open(s.n, 'c') as b:
            for x in u:
                if x in b:
                    v, p = ecc.b2i(b[x][:4]), ecc.b2i(b[x][4:])
                    if   p == u[x][2]: assert v == u[x][1]
                    elif p >  u[x][2]: assert v >  u[x][1]
                    else: b[x] = u[x][0]
                else:     b[x] = u[x][0]
            for x in [y for y in t if t[y] > (ecc.b2i(b[y]) if y in b else 0)]: b[x] = ecc.i2b(t[x], 4) 

    def pos(s, z):
        with dbm.open(s.n) as b:
            return b[z][4:] if z in b else ecc.z2

    def reset(s):
        with dbm.open(s.n, 'c') as b:
            for x in b.keys(): del b[x]
            k = ecc.ecdsa()
            k.generate()
            s.pk = k.compress(k.pt)          # My Public  key
            b[b'&'] = ecc.i2b(k.privkey, 48) # My Private key
            
    def savepks(s):
        with dbm.open(s.n, 'c') as b:
            for x in s.tpk: b[b'#'+x] = s.tpk[x] # Others Public keys

    def getsk(s):
        with dbm.open(s.n) as b: return ecc.b2i(b[b'&']) # Authentication

    def server(s):
        t = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        for x in range(MAXP):
            try:
                t.bind((HOST, BASP+x))
                break
            except: pass
        s.p = x
        print (s.n, 'using port', s.p + BASP, '(please (i)nitialize)')        
        while True:
            m, a = t.recvfrom(1024)
            if   m == b'?': t.sendto(s.pk + s.n.encode('utf-8'), a)
            elif len(m) > SLEN: print (s.manage(m, a))

    def manage(s, m, a=None):
        t, k = socket.socket(socket.AF_INET, socket.SOCK_DGRAM), ecc.ecdsa()
        k.pt, dst = k.uncompress(m[:5] + s.tpk[m[:5]]), s.rvs[m[5:10]]         
        if m[5:10] != s.tid[s.n]              : return False
        if not k.verify(m[-SLEN:], m[:-SLEN]) : return False
        if s.pos(m[:10]) != m[14:16]          : return False
        s.add(m[:MLEN])
        s.update(m[MLEN:-SLEN])
        t.sendto(s.sta(), a)
        return True

    def sendpk(s, dst, m):
        t = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        t.sendto(m, (HOST, s.tbl[s.rvs[dst]]))

    def http(s, arg):
        print('Serving', HOST, s.p + BASP)
        srv = socketserver.TCPServer((HOST, s.p + BASP), handler)
        srv.RequestHandlerClass.nod = arg
        srv.serve_forever()

    def register(s):
        print('Backend')
        socketserver.TCPServer((HOST, BPRT), handler).serve_forever()

class handler(http.server.BaseHTTPRequestHandler):    
    nod = None
    def response(s, mime):
        s.send_response(200)
        s.send_header('Content-type', mime)
        s.end_headers()

    def do_GET(s): 
        s.response('text/plain; charset=utf-8')
        if s.nod == None:
            s.wfile.write(b'Backend\n') 
        else:
            with dbm.open(s.nod.n) as b:
                s.wfile.write(b'User:' + s.nod.n.encode('utf-8') + b'\nMatrix:\n')
                for x in b.keys(): s.wfile.write(b'%d:%d\n' % (len(x), len(b[x])))
                s.wfile.write(b'Balance: %d\n' % s.nod.bal(s.nod.n))
                s.wfile.write(('Check: %s\n' % s.nod.check()).encode('utf-8'))

def reg(v):
    reg.v = v
    return v

def run_test():
    ppl, p = {'alice':-94, 'bob':87, 'carol':4, 'dave':3}, {} # Expected balances with tax=20%
    for x in ppl: p[x] = pexpect.spawnu(__file__ + ' ' + x); p[x].expect('>')
    for x in ppl: p[x].sendline('i'); p[x].expect('>')    # Initialize
    p['alice'].sendline('bob100'); p['alice'].expect('>') # Alice pays 100 to Bob
    p['carol'].sendline('alice1'); p['carol'].expect('>') # Carol pays 1   to Alice
    p['dave' ].sendline('bob  2'); p['dave' ].expect('>') # Dave  pays 2   to Bob
    for x in ppl: p[x].sendline('c'); p[x].expect('>')    # Check balances
    for x in ppl: p[x].sendline('b'); p[x].expect('%s\(%d\)>' % (x.upper(), ppl[x])) # Final test

if __name__ == '__main__':
    if len(ecc.sys.argv) == 2: node(ecc.sys.argv[1].upper())
    else: run_test()
    
# End ⊔ TEN!
