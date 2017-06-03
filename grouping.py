from charm.toolbox.ecgroup import ECGroup, G, ZR
from charm.toolbox.eccurve import prime192v1, prime192v2
from charm.core.math.integer import integer, toInt
import random
from functools import reduce

# utility functions

def random_point(group):
    return group.random(G)

def random_number(group):
    return group.random()

def make_pi(n):
    xs = range(n)
    random.shuffle(xs)
    return xs

def make_sigma(n, m):
    return make_pi(n - m) 

def permute(pi, d):
    assert len(pi) == len(d)
    return [d[i] for i in pi]

def compose(pi2, pi1):
    assert len(pi1) == len(pi2)
    return [pi1[i] for i in pi2]

def inverse(pi):
    xs = [(pi[i], i) for i in range(len(pi))]
    return [x[1] for x in sorted(xs)]

def mask(s):
    return [random.choice([True, False]) for _ in range(s)]

def transform(pi):
    return [p for (_, p) in sorted(zip(pi, range(len(pi))))]

def minus1(pi):
    return [p - 1 for p in pi]

# class

class Player:
    # n - the number of cards
    # m - the number of groups
    def __init__(self, group, n, m):
        self.key = group.random(ZR)
        self.pi1 = make_pi(n)
        self.pi2 = make_sigma(n, m)

# operation

def procedure_32(group, deck, p):
    assert len(p) == len(deck)
    r = [ random_number(group) for _ in range(len(deck)) ]
    c = [(x[0][0] ** x[1], x[0][1] ** x[1]) for x in zip(deck, r)]
    return (permute(p, c), r, p)

def procedure_33(n, m, ca, cb, r, pi):
    def f(i):
        db_i, ab_i = cb[i]
        da_i, aa_i = ca[pi[i]]
        r_i        = r[pi[i]]
        return db_i == (da_i ** r_i) and ab_i == (aa_i ** r_i)

    return all( f(i) for i in range(n - m) )

def procedure_34(group, deck):
    rs = [random_number(group) for _ in range(len(deck))]
    c = [(x[0] ** r, x[1] ** r) for (x, r) in zip(deck, rs)]
    return (c, rs)
            
def protocol_48(group, n, m, p, ci_1, ci, pi, r, s):
    c = [procedure_32(group, ci, p) for _ in range(s)]
    u = mask(s)
    def f(i):
        c_ik, r_ik, pi_ik = c[i]
        if u[i]:
            return procedure_33(n, m, ci, c_ik, r_ik, pi_ik)
        else:
            pi_ = compose(pi_ik, pi)
            r_  = permute(inverse(pi_), [r[pi_[j]] * r_ik[pi_ik[j]] for j in range(len(pi_))])
            return procedure_33(n, m, ci_1, c_ik, r_, pi_)

    return all([f(i) for i in range(s)])
    

def cp_proof(alpha, beta, er, er_1, c, r, a, b):
    return alpha ** r == a * (beta ** c) and er ** r == b * (er_1 ** c)

def protocol_47a(group, n, m, d, players, s = 10):
    ci_1 = d
    for p in players:
        ci, ri, pii = procedure_32(group, ci_1, p.pi1)
        assert protocol_48(group, n, m, make_pi(n), ci_1, ci, pii, ri, s)
        ci_1 = ci
    return ci_1

def protocol_47b(group, n, m, d, players, s = 10):
    ci_1 = d
    for p in players:
        ci, ri, pii = procedure_32(group, ci_1, p.pi2)
        assert protocol_48(group, n, m, make_sigma(n, m), ci_1, ci, pii, ri, s)
        ci_1 = ci
    return ci_1

def protocol_50(group, c2, players):
    c_a = c2
    for p in players:
        c, _ = procedure_34(group, c_a)
        # need to verify
        c_a = c
    return c_a

def protocol_51(group, n, m, i, ps, xs, sigma_c, sigma_d, tau):
    taun = reduce(lambda acc, _: compose(tau, acc), range(i), tau)
    taun_sigma_d = permute(taun, sigma_d)

    r_sigma_c, r_taun_sigma_d = protocol_47a(group, n, m, sigma_c, ps), protocol_47a(group, n, m, taun_sigma_d, ps)
     
    r_sigma = [draw(group, r_sigma_c, xs, i, ps) for i in range(n)]
    sigmainv_rinv = inverse(r_sigma)

    sigmainv_taun_sigma_d = permute(sigmainv_rinv, r_taun_sigma_d)

    return sigmainv_taun_sigma_d

def draw(group, deck, xs, i, ps):
    assert i < len(deck)

    def fn_er(er_1, p):
        er = er_1 ** (p.key ** -1)
        for p_ in ps:
            if not p_ is p:
                s, c = random_number(group), random_number(group)
                a, b = room.alpha ** s, er ** s
                r = p.send_r(s, c)
                assert cp_proof(room.alpha, p.beta, er, er_1, c, r, a, b)
        return er

    d, a = deck[i]
    en   = reduce(lambda acc, p: acc ** (p.key ** -1), ps, a)
    
    def get_card(xs):
        for x, i in zip(xs, range(len(xs))):
            if en ** x == d:
                return i
        return -1
    
    c = get_card(xs)
    assert c > -1
    return c


if __name__ == "__main__":
    # ecc group
    group = ECGroup(prime192v1)

    # the number of cards
    n = 7
    # the number of groups
    m = 3
    # max of the number of group member
    r = 2
    # the number of players
    p = n - m

    tau = transform(minus1([2, 5, 6, 7, 1, 3, 4]))
    #tau = [1, 4, 5, 6, 0, 2, 3]
    #tau = [1, 2, 5, 4, 6, 0, 3]
    #tau = [6, 0, 7, 2, 8, 4, 1, 3, 5]

    # players
    ps = [Player(group, n, m) for _ in range(p)]

    # public key
    alpha = random_point(group)
    # use dh key exchange
    beta = reduce(lambda x, y: x ** y.key, ps, alpha)

    x1, x2 = [random_number(group) for _ in range(p)], [random_number(group) for _ in range(m)]
    y1, y2 = [random_number(group) for _ in range(p)], [random_number(group) for _ in range(m)]
    c01, c02 = [(alpha ** x1[i], beta) for i in range(p)], [(alpha ** x2[i], beta) for i in range(m)]
    d01, d02 = [(alpha ** y1[i], beta) for i in range(p)], [(alpha ** y2[i], beta) for i in range(m)]

    sigma_c1, sigma_d1 = protocol_47b(group, n, m, c01, ps), protocol_47b(group, n, m, d01, ps)
    c2, d2 = protocol_50(group, c02, ps), protocol_50(group, d02, ps)
    
    ds = [protocol_51(group, n, m, i, ps, x1 + x2, sigma_c1 + c2, sigma_d1 + d2, tau) for i in range(r)]
    
    for d in ds:
        cs = [draw(group, d, y1 + y2, i, ps) for i in range(n)]
        print(cs)
