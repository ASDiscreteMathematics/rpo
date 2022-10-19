# rescue_prime_optimized.sage
# The reference implementation of Rescue-Prime Optimized.

from CompactFIPS202 import SHAKE256

def get_round_constants( security_level ):
    assert(security_level == 128 or security_level == 160)
    # basic parameters
    if security_level == 128:
        m = 12
        capacity = 4
    else:
        m = 16
        capacity = 6
    p = 2^64 - 2^32 + 1
    N = 7
    # generate pseudorandom bytes
    bytes_per_int = ceil(len(bin(p)[2:]) / 8) + 1
    num_bytes = bytes_per_int * 2 * m * N
    seed_string = "RPO(%i,%i,%i,%i)" % (p, m, capacity, security_level)
    byte_string = SHAKE256(bytes(seed_string, "ascii"), num_bytes)

    # process byte string in chunks
    round_constants = []
    Fp = FiniteField(p)
    for i in range(2*m*N):
        chunk = byte_string[bytes_per_int*i : bytes_per_int*(i+1)]
        integer = sum(256^j * ZZ(chunk[j]) for j in range(len(chunk)))
        round_constants.append(Fp(integer % p))

    return round_constants

def get_alphas( ):
    p = 2^64 - 2^32 + 1
    alpha = 7
    g, alphainv, garbage = xgcd(alpha, p-1)
    return (alpha, (alphainv % (p-1)))

def get_mds( m ):
    assert(m == 12 or m == 16)
    p = 2^64 - 2^32 + 1
    Fp = FiniteField(p)
    if m == 12:
        return [Fp(i) for i in [7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8]]
    if m == 16:
        return [Fp(i) for i in [256, 2, 1073741824, 2048, 16777216, 128, 8, 16, 524288, 4194304, 1, 268435456, 1, 1024, 2, 8192]]

def mds_matrix_vector_multiplication(mds, state):
    mat = matrix.circulant(mds)
    vec = matrix([state]).transpose()
    new_vec = mat * vec
    return [new_vec[i, 0] for i in range(new_vec.nrows())]

def ntt( array, omega, order ):
    return [sum(omega^(i*j) * array[j] for j in range(order)) for i in range(order)]

def intt( array, omega, order ):
    p = 2^64 - 2^32 + 1
    Fp = FiniteField(p)
    return [Fp(order)^-1 * a for a in ntt(array, omega^-1, order)]

def mds_ntt(mds, state):
    p = 2^64 - 2^32 + 1
    Fp = FiniteField(p)
    order = len(state)
    if order == 12:
        omega = Fp(281474976645120)
    else:
        omega = Fp(17293822564807737345)
    assert(omega.multiplicative_order() == order)

    setat = [state[0]] + [a for a in reversed(state[1:])]

    aa = ntt(mds, omega, order)
    bb = ntt(setat, omega, order)
    cc = [a*b for (a,b) in zip(aa, bb)]

    ptcudor = intt(cc, omega, order)
    return [ptcudor[0]] + [a for a in reversed(ptcudor[1:])]

def karatsuba(lhs, rhs):
    assert(len(lhs) == len(rhs))
    if len(lhs) == 1:
        return [lhs[0] * rhs[0]]

    zero = lhs[0] - lhs[0]

    half = ceil(len(lhs) / 2)
    lhs_left = lhs[:half]
    lhs_right = lhs[half:]
    rhs_left = rhs[:half]
    rhs_right = rhs[half:]

    if len(lhs_right) < len(lhs_left):
        lhs_right += [zero]
        rhs_right += [zero]

    lhs_sum = [a+b for (a,b) in zip(lhs_left, lhs_right)]
    rhs_sum = [a+b for (a,b) in zip(rhs_left, rhs_right)]

    z0 = karatsuba(lhs_left, rhs_left)
    z2 = karatsuba(lhs_right, rhs_right)
    z1 = [a - b - c for (a,b, c) in zip(karatsuba(lhs_sum, rhs_sum), z0, z2)]

    product = [zero] * (len(lhs) + len(rhs) - 1)
    for i in range(len(z0)):
        product[i] = z0[i]
    for i in range(len(z1)):
        product[half+i] += z1[i]
    for i in range(len(z2)):
        if 2*half+i >= len(product):
            # len(product) is odd
            break
        product[2*half+i] += z2[i]

    return product

def mds_karatsuba(mds, state):
    msd = [mds[0]] + [a for a in reversed(mds[1:])]
    conv = karatsuba(msd, state)
    for i in range(len(mds), len(conv)):
        conv[i-len(mds)] += conv[i]
    return conv[:len(mds)]

def rpo_hash( security_level, input_sequence ):
    assert(len(input_sequence) > 0)
    assert(security_level == 128 or security_level==160)

    # get parameters
    p = 2^64 - 2^32 + 1
    if security_level == 128:
        m = 12
        capacity = 4
    else:
        m = 16
        capacity = 6
    MDS = get_mds(m)
    alpha, alphainv = get_alphas()
    N = 7
    round_constants = get_round_constants(security_level)
    parameters = (p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants)
    rate = m - capacity
    Fp = FiniteField(p)

    state = [Fp(0)] * m

    if len(input_sequence) % rate != 0:
        # pad
        padded_input = input_sequence + [Fp(1)]
        while len(padded_input) % rate != 0:
            padded_input.append(Fp(0))
        # set domain separation bit
        state[0] = Fp(1)
    else:
        padded_input = input_sequence

    # divide into chunks of rate and absorb
    while padded_input:
        state[capacity:capacity+rate] = padded_input[:rate] # overwrite mode
        state = rescue_XLIX_permutation(parameters, state)
        padded_input = padded_input[rate:]

    # squeeze once, truncate to length
    return state[capacity:capacity+rate//2]

def rescue_XLIX_permutation( parameters, state ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    Fp = state[0].parent()

    # pick one
    mds = lambda vec : mds_matrix_vector_multiplication(MDS, vec)
    #mds = lambda vec : mds_ntt(MDS, vec)
    #mds = lambda vec : mds_karatsuba(MDS, vec)

    for i in range(N):
        # mds
        state = mds(state)
        # constants
        for j in range(m):
            state[j] += round_constants[i*2*m+j]
        # S-box
        for j in range(m):
            state[j] = state[j]^alpha

        # mds
        state = mds(state)
        # constants
        for j in range(m):
            state[j] += round_constants[i*2*m+m+j]
        # inverse S-box
        for j in range(m):
            state[j] = state[j]^alphainv

    return state

def print_test_vectors( security_level ):
    assert(security_level == 128 or security_level == 160)
    p = 2^64 - 2^32 + 1
    Fp = FiniteField(p)
    for i in range(1,20):
        input_sequence = [Fp(j) for j in range(i)]
        output_sequence = rpo_hash(security_level, input_sequence)
        print(matrix([input_sequence]), " -> ", matrix([output_sequence]))


