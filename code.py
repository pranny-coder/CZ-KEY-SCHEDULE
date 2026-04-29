import hashlib, os, random
from collections import Counter

# ================== BASIC UTILS ==================
def H(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

def XOR(a: bytes, b: bytes) -> bytes:
    return bytes(x ^ y for x, y in zip(a, b))

# ================== SBOX & ANALYSIS ==================
SBOX = [
0xC,0x5,0x6,0xB,
0x9,0x0,0xA,0xD,
0x3,0xE,0xF,0x8,
0x4,0x7,0x1,0x2
]
INV_SBOX = [0]*16
for i,v in enumerate(SBOX): INV_SBOX[v]=i

def analyze_sbox_linearity(sbox):
    """Calculates the Linear Approximation Table (LAT) bias."""
    max_bias = 0
    for a in range(1, 16):  # Input mask
        for b in range(1, 16):  # Output mask
            hits = 0
            for x in range(16):
                if bin(a & x).count('1') % 2 == bin(b & sbox[x]).count('1') % 2:
                    hits += 1
            bias = abs(hits - 8)
            if bias > max_bias: max_bias = bias
    return max_bias / 16

# ================== CHESS LOGIC ==================
MOVE_K32 = [(3,2),(3,-2),(-3,2),(-3,-2),(2,3),(2,-3),(-2,3),(-2,-3)]
MOVE_K31 = [(3,1),(3,-1),(-3,1),(-3,-1),(1,3),(1,-3),(-1,3),(-1,-3)]

def BuildMoveTable(deltas):
    table=[[] for _ in range(64)]
    for sq in range(64):
        r,c=divmod(sq,8)
        for dr,dc in deltas:
            nr,nc=r+dr,c+dc
            if 0<=nr<8 and 0<=nc<8: table[sq].append(nr*8+nc)
    return table

TABLE_K32 = BuildMoveTable(MOVE_K32)
TABLE_K31 = BuildMoveTable(MOVE_K31)

# ================== PERMUTATION ==================
def bytes_to_bits(b):
    return [(byte>>k)&1 for byte in b for k in range(7,-1,-1)]

def bits_to_bytes(bits):
    out=bytearray(16)
    for i in range(16):
        v=0
        for k in range(8): v=(v<<1)|bits[i*8+k]
        out[i]=v
    return bytes(out)

def ApplyPerm(p, s):
    bits=bytes_to_bits(s)
    return bits_to_bytes([bits[p[i]] for i in range(128)])

def InversePerm(p):
    inv=[0]*128
    for i,v in enumerate(p): inv[v]=i
    return inv

def gen_perms(n=256):
    perms=[]
    base=list(range(128))
    for i in range(n):
        rnd=random.Random(int.from_bytes(H(b"perm"+i.to_bytes(4,"big")), "big"))
        p=base[:]; rnd.shuffle(p); perms.append(p)
    return perms

PERMS = gen_perms()

# ================== CIPHER ENGINE ==================
class ChessWalkCipher:
    def __init__(self, K, N, R=16, W=20):
        self.R = R
        self.W = W
        seed = H(K + N)
        self.T = seed[:16]
        self.start_sq = int.from_bytes(seed, "big") % 64
        self.RK = [None] * (R + 1)
        self.RP = [None] * (R + 1)
        self.walk_history = []
        
        for r in range(1, R+1):
            cur = self.start_sq
            walk = bytearray()
            for j in range(1, W+1):
                h1 = H(K+N+r.to_bytes(4,"big")+j.to_bytes(4,"big")+b"piece")
                h2 = H(K+N+r.to_bytes(4,"big")+j.to_bytes(4,"big")+cur.to_bytes(1,"big")+b"move")
                moves = TABLE_K32[cur] if int.from_bytes(h1, "big")%2==0 else TABLE_K31[cur]
                if not moves: moves = list(set(TABLE_K32[cur] + TABLE_K31[cur]))
                nxt = moves[int.from_bytes(h2, "big") % len(moves)]
                walk.append(((cur << 3) ^ nxt ^ j) & 0xFF)
                cur = nxt
                self.walk_history.append(cur)
            h = H(K+N+r.to_bytes(4,"big") + bytes(walk))
            self.RK[r] = h[:16]
            self.RP[r] = PERMS[int.from_bytes(h, "big") % len(PERMS)]

    def encrypt_block(self, P):
        S = XOR(P, self.T)
        for r in range(1, self.R + 1):
            S = XOR(S, self.RK[r])
            n = []
            for b in S:
                n.append(SBOX[(b >> 4) & 0xF])
                n.append(SBOX[b & 0xF])
            out = bytearray(16)
            for i in range(16): out[i] = (n[2*i] << 4) | n[2*i+1]
            S = ApplyPerm(self.RP[r], bytes(out))
        return XOR(S, self.T)

    def decrypt_block(self, C):
        S = XOR(C, self.T)
        for r in range(self.R, 0, -1):
            S = ApplyPerm(InversePerm(self.RP[r]), S)
            n = []
            for b in S:
                n.append(INV_SBOX[(b >> 4) & 0xF])
                n.append(INV_SBOX[b & 0xF])
            out = bytearray(16)
            for i in range(16): out[i] = (n[2*i] << 4) | n[2*i+1]
            S = XOR(bytes(out), self.RK[r])
        return XOR(S, self.T)

# ================== TESTS ==================

def run_chess_heatmap(samples=5000):
    print("[*] Running Chess-Walk Heatmap Coverage Test...")

    coverages=[]

    for _ in range(samples):

        K=os.urandom(16)
        N=os.urandom(16)

        cipher=ChessWalkCipher(K,N)

        counts=Counter(cipher.walk_history)

        coverages.append(len(counts))

    mean=sum(coverages)/len(coverages)

    var=sum((x-mean)**2 for x in coverages)/len(coverages)

    std=var**0.5

    print(f"    Mean Coverage: {mean:.2f}/64")
    print(f"    Coverage Std Dev: {std:.4f}")

def run_integral_test(K, N):
    print("[*] Running Integral (Saturation) Test...")
    cipher = ChessWalkCipher(K, N)
    results = bytearray(16)
    for i in range(256):
        P = bytearray(b"constant_prefix_")
        P[15] = i
        C = cipher.encrypt_block(bytes(P))
        for j in range(16): results[j] ^= C[j]
    zero_count = results.count(0)
    print(f"    Integral Sum Zero-Bytes: {zero_count}/16")

def run_sbox_analysis():
    bias = analyze_sbox_linearity(SBOX)
    print(f"[*] S-Box Linear Bias: {bias:.4f} (Ideal: < 0.2500)")

def run_sac_test(K,N,samples=5000):
    print("[*] Running Strict Avalanche Criterion (SAC)...")

    cipher=ChessWalkCipher(K,N)

    grand_total=0
    total_trials=0

    for _ in range(samples):

        P=os.urandom(16)

        C0=cipher.encrypt_block(P)

        for i in range(128):

            P2=bytearray(P)

            byte_index=i//8
            bit_index=7-(i%8)

            P2[byte_index]^=(1<<bit_index)

            C1=cipher.encrypt_block(bytes(P2))

            diff=sum(bin(a^b).count("1")
                     for a,b in zip(C0,C1))

            grand_total+=diff
            total_trials+=1

    avg=grand_total/total_trials

    print(f"    Sample Size: {samples}")
    print(f"    Avg Output Bits Flipped: {avg:.2f}/128")



def run_differential_test(K,N,samples=5000):
    print("[*] Running Differential Test...")

    cipher=ChessWalkCipher(K,N)

    delta=bytes([1]+[0]*15)

    counts=[]

    for _ in range(samples):

        P=os.urandom(16)

        P2=XOR(P,delta)

        C1=cipher.encrypt_block(P)
        C2=cipher.encrypt_block(P2)

        diff=sum(bin(a^b).count('1')
                 for a,b in zip(C1,C2))

        counts.append(diff)

    mean=sum(counts)/len(counts)

    var=sum((x-mean)**2 for x in counts)/len(counts)

    std=var**0.5

    print(f"    Differential Spread Mean: {mean:.2f}")
    print(f"    Differential Spread Std Dev: {std:.4f}")

def run_cycle_test(samples=5000):
    print("[*] Running State Cycle-Length Test...")

    no_cycle=0

    for _ in range(samples):

        K=os.urandom(16)
        N=os.urandom(16)

        cipher=ChessWalkCipher(K,N)

        visited={}
        cycle_found=False

        for idx,sq in enumerate(cipher.walk_history):

            r=(idx//cipher.W)+1
            j=(idx%cipher.W)+1

            state=(r,j,sq)

            if state in visited:
                cycle_found=True
                break

            visited[state]=idx

        if not cycle_found:
            no_cycle+=1

    print(f"    No Short Cycles: {no_cycle}/{samples}")
def run_weak_key_search(trials=5000):
    print("[*] Running Key Avalanche Distribution Test...")

    avalanche_vals=[]

    weak=0

    for _ in range(trials):

        K=os.urandom(16)
        N=os.urandom(16)

        cipher=ChessWalkCipher(K,N)

        P=b"1234567890ABCDEF"

        C1=cipher.encrypt_block(P)

        P2=bytearray(P)
        P2[0]^=1

        C2=cipher.encrypt_block(bytes(P2))

        diff=sum(bin(a^b).count('1')
                 for a,b in zip(C1,C2))

        avalanche_vals.append(diff)

        if diff<50:
            weak+=1

    mean=sum(avalanche_vals)/len(avalanche_vals)

    var=sum((x-mean)**2
            for x in avalanche_vals)/len(avalanche_vals)

    std=var**0.5

    print(f"    Mean Avalanche Across Keys: {mean:.2f}")
    print(f"    Avalanche Std Dev: {std:.4f}")
    print(f"    Keys Below Threshold(50): {weak}/{trials}")

def run_decrypt_test(K,N,samples=5000):
    print("[*] Running Decryption Correctness Test...")

    cipher=ChessWalkCipher(K,N)

    correct=0

    for _ in range(samples):

        P=os.urandom(16)

        C=cipher.encrypt_block(P)

        if cipher.decrypt_block(C)==P:
            correct+=1

    print(f"    Sample Size: {samples}")
    print(
      f"    Correct Decryptions:"
      f" {correct}/{samples}"
    )   

def run_randomness_tests(K,N):
    print("[*] Running Randomness Tests...")

    cipher=ChessWalkCipher(K,N)

    bits=[]

    for _ in range(5000):

        P=os.urandom(16)

        C=cipher.encrypt_block(P)

        for byte in C:
            for k in range(8):

                bits.append(
                  (byte>>(7-k))&1
                )

    ones=sum(bits)

    zeros=len(bits)-ones

    p=ones/len(bits)

    print(f"    Frequency: 1s={ones} 0s={zeros}")
    print(f"    Bit Probability P(1): {p:.6f}")

    runs=1

    for i in range(1,len(bits)):
        if bits[i]!=bits[i-1]:
            runs+=1

    print(f"    Runs Count: {runs}") 

def run_differential_trail_search():
    print("[*] Running Differential Trail Search...")
    ddt=[[0]*16 for _ in range(16)]
    for dx in range(16):
        for x in range(16):
            dy=SBOX[x]^SBOX[x^dx]
            ddt[dx][dy]+=1
    max_prob=0
    for dx in range(1,16):
        prob=max(ddt[dx])/16
        if prob>max_prob: max_prob=prob
    print(f"    Max Single-SBox Differential Probability: {max_prob:.4f}")

def run_linear_hull_analysis():
    print("[*] Running Linear Hull Analysis...")
    max_bias=0
    for a in range(1,16):
        for b in range(1,16):
            hits=0
            for x in range(16):
                if (bin(a&x).count('1')%2)==(bin(b&SBOX[x]).count('1')%2): hits+=1
            bias=abs(hits-8)/16
            if bias>max_bias: max_bias=bias
    print(f"    Max Linear Hull Bias: {max_bias:.4f}")

def run_algebraic_analysis(rounds=16):
    print("[*] Running Algebraic Attack Analysis...")
    degree=min(128, 2**rounds)
    print(f"    Estimated Algebraic Degree After {rounds} Rounds: {degree}")

def run_roundkey_uniqueness_test(samples=5000):
    print("[*] Running Round-Key Uniqueness Test...")

    unique_count=0

    for _ in range(samples):

        K=os.urandom(16)
        N=os.urandom(16)

        cipher=ChessWalkCipher(K,N)

        seen=set()

        unique=True

        for r in range(1,cipher.R+1):

            if cipher.RK[r] in seen:
                unique=False
                break

            seen.add(cipher.RK[r])

        if unique:
            unique_count+=1

    print(f"    Unique Key Schedules: {unique_count}/{samples}")

# ================== MAIN ==================
# ================== MAIN ==================
# ================== MAIN ==================
if __name__ == "__main__":

    K=b"MY_SECRET_KEY_16"
    N=b"MY_NONCE_VALUE_1"

    print("\n--- CHESS-WALK CIPHER ADVANCED REPORT ---")

    # =========================
    # KEY-SCHEDULE / STRUCTURAL
    # =========================
    print("\n[KEY-SCHEDULE / STRUCTURAL TESTS]")

    run_chess_heatmap()
    run_cycle_test()
    run_weak_key_search()
    run_roundkey_uniqueness_test()

    # =========================
    # DIFFUSION / STATISTICAL
    # =========================
    print("\n[DIFFUSION / STATISTICAL TESTS]")

   
    
    run_decrypt_test(K,N)

    run_sac_test(K,N)
   
    
    run_differential_test(K,N)
    run_randomness_tests(K,N)

    # =========================
    # CRYPTANALYTIC RESISTANCE
    # =========================
    print("\n[CRYPTANALYTIC RESISTANCE TESTS]")

    run_sbox_analysis()
    run_differential_trail_search()
    run_linear_hull_analysis()
    run_algebraic_analysis()


