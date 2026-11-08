-- Prove2me | Theorems.Thm_EntangledPIR_theorem_5_1_main
-- name    : EntangledPIR.theorem_5_1_main
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:48.505223+00:00
-- url     : https://prove2.me/theorems/92b348e7-c02a-4657-89dd-d2d78cde07dc
-- title:
--   Theorem 5.1 (Main Theorem) — Protocol 1 is correct, $2^{-\lambda}$-private against A, perfectly private against B, and efficient
-- statement:
--   Let $n,m,\lambda\ge1$ be integers, $k=n\lambda+1$, and $w=\lceil\log(k+1)\rceil$. For every database $F:\{0,1\}^n\to\{0,1\}^m$, Protocol 1 has the following properties.
--
--   1. **Correctness.** If both servers follow the protocol, starting from $4k(nw+m2^{nw})$ Bell pairs, the client outputs $F(x)$ with probability one for every index $x$.
--   2. **Privacy.** The protocol is $2^{-\lambda}$-private against A and perfectly private against B.
--   3. **Efficiency.** The client is the same for every database and runs in time polynomial in $n,m,\lambda$. The protocol has a constant number of rounds, and in the honest execution it communicates $2m+O(n^2\lambda\log(n\lambda+2))$ bits, of which $2m+8knw$ are sent by the servers. The number of Bell pairs and the number of elementary operations of each honest server are at most $m\cdot2^{O(n\log(n\lambda+2))}$.
--
--   Privacy holds for every initial state of the servers, which need not be Bell pairs and may be entangled across all copies, for every strategy of the malicious server, at every round, and for the view not conditioned on acceptance.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: the view, including timing and termination (p.11, A.1) → a classical-quantum matrix on history × register, after every round $r\le 4$, with a fixed schedule that continues with empty messages after an abort, and $r=0$ included; reason: the round is the timing; abort shows in the history; later operations are channels independent of the index and idle strategies recover the view at the end of the execution; at $r=0$ the two views coincide
--   - encoding: $\mathbb F_{2^w}$ with any fixed basis containing 1 (p.24) → the concrete field of App. C.2: first irreducible polynomial, polynomial basis, Fermat inverse, $\alpha_i$ the binary representation of $i$; reason: App. C.2 fixes this choice for the client; the multilinear extension is given by the standard formula of p.57
--   - encoding: each $O(\cdot)$ → one absolute real constant $C>0$ before $n,m,\lambda$; reason: the meaning of a uniform $O(\cdot)$; the arithmetic holds for all $n,m,\lambda\ge1$ (p.57)
--   - encoding: polynomial running time, memory, random bits; uniform; the same for every database; no oracle query → one machine in `TM2ComputableInPolyTime` for `clientStep` on an injective encoding with unary $n,m,\lambda$, a polynomial bound on the input length for every message in the alphabet, and a bound on `tapeLen`; reason: memory is at most input length plus time; `clientStep` has no database and no oracle in its type
--   - encoding: the communication of the honest execution → counted on every branch of nonzero trace of the honest execution; reason: these are the branches that occur
--   - encoding: the number of Bell pairs; their preparation does not depend on $F$ → `Fintype.card (BellIdx n m lam)`, and `bellVector` with no database in its type; reason: the qubits of the state are that index type (verified in the sanity file)
--   - encoding: an elementary operation → `ElemOp`: Hadamard, Pauli X, CNOT, Toffoli, measurement of one qubit, classical bit operation, each with at most one classical control cell, with ancillas returned to zero, and the outgoing message read from a fixed memory slot; reason: classical control is what A.1 and Claim C.3 describe, at constant overhead
--   - generalization: each honest server performs its operations for the database → one list of operations for all databases (`ServerImpl`), reading the tables as classical control from a memory computed by a bit-operation list from the truth table of $F$; reason: fixing $F$ gives a list for that database; the database is read-only classical control (A.1), and the proof (pp.57–58) counts the table computation
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Theorem 5.1, pp.23–24

import Definitions.Def_EntangledPIR_PrivateAgainstA
import Definitions.Def_EntangledPIR_ServerImpl
import Definitions.Def_EntangledPIR_encClientInput

namespace EntangledPIR

/-- **Theorem 5.1 (Main Theorem)**, Mantri, manuscript (Nov. 2026), pp.23–24. Let `n, m, λ ≥ 1`, `k = nλ + 1`,
`w = ⌈log(k + 1)⌉`. For every database `F : {0,1}^n → {0,1}^m`, Protocol 1 has the following properties.

(i) Correctness. If both servers follow the protocol, starting from `4k(nw + m 2^{nw})` Bell pairs, the client outputs
`F(x)` with probability one for every index `x`.

(ii) Privacy. The protocol is `2^{-λ}`-private against A and perfectly private against B.

(iii) Efficiency. The client is the same for every database and runs in time polynomial in `n, m, λ`. The protocol has a
constant number of rounds, and in the honest execution it communicates `2m + O(n²λ log(nλ + 2))` bits, of which
`2m + 8knw` are sent by the servers. The number of Bell pairs and the number of elementary operations of each honest
server are at most `m · 2^{O(n log(nλ+2))}`.

**Formalization Note.** `C`, the polynomial `q` and the client's machine come before `n, m, λ`, and the machine computes
`clientStep`, in whose type no database occurs. The implementation `P` comes before `F`. `PrivateAgainstA` fixes the
initial state and the strategy before the indices. -/
theorem theorem_5_1_main :
    ∃ (C : ℝ) (q : Polynomial ℕ), 0 < C ∧
      Nonempty (Turing.TM2ComputableInPolyTime encClientInput encClientOutput clientStep) ∧
      ∀ n m lam : ℕ, 1 ≤ n → 1 ≤ m → 1 ≤ lam →
        (tapeLen n lam ≤ q.eval (n + m + lam) ∧
          ∀ (x tape : List Bool) (srv : List (List Bool × List Bool)),
            x.length = n → tape.length = tapeLen n lam → srv.length ≤ numRounds →
            (∀ p ∈ srv, p.1.length ≤ msgBound n m lam ∧ p.2.length ≤ msgBound n m lam) →
            (encClientInput ⟨n, m, lam, x, tape, srv⟩).length ≤ q.eval (n + m + lam)) ∧
        (numRounds : ℝ) ≤ C ∧
        (Fintype.card (BellIdx n m lam) =
            4 * shareCount n lam * (n * fieldWidth n lam + m * 2 ^ (n * fieldWidth n lam)) ∧
          ((Fintype.card (BellIdx n m lam) : ℕ) : ℝ) ≤
            m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2))) ∧
        (∃ P : ServerImpl n m lam, P.Correct ∧
          ((P.opsA : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2)) ∧
          ((P.opsB : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2))) ∧
        ∀ F : Bits n → Bits m,
          (∀ x, successProb lam F x = 1) ∧
          PrivateAgainstA lam F ((2 : ℝ) ^ lam)⁻¹ ∧
          PrivateAgainstB lam F 0 ∧
          (∀ (x : Bits n) (tape : Bits (tapeLen n lam))
            (τ : Transcript (msgBound n m lam) numRounds),
            Matrix.trace (honestState lam F (List.ofFn x) (List.ofFn tape) numRounds τ) ≠ 0 →
            serverBits τ = 2 * m + 8 * shareCount n lam * (n * fieldWidth n lam) ∧
            ((commBits n m lam (List.ofFn x) (List.ofFn tape) τ : ℕ) : ℝ) ≤
              2 * m + C * n ^ 2 * lam * Real.logb 2 (n * lam + 2)) := by sorry

end EntangledPIR
