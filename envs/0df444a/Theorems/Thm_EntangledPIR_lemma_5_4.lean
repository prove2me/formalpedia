-- Prove2me | Theorems.Thm_EntangledPIR_lemma_5_4
-- name    : EntangledPIR.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:55.936674+00:00
-- url     : https://prove2.me/theorems/9b657c6c-e1bf-4609-bbaf-105f7f924f62
-- title:
--   Lemma 5.4 — communication and resources
-- statement:
--   Let $n,m,\lambda\ge1$, let $k$, $w$, $d=nw$ be as in (5.1), and let $F$ be a database.
--
--   1. The client of Protocol 1 is uniform and the same for every database, and it makes no oracle query. On every execution, for all messages of the servers, its running time, memory and number of random bits are polynomial in $n,m,\lambda$.
--   2. The protocol has a constant number of rounds. The answers of honest servers contain $2m+8knw$ bits, and the total communication, in bits, is
--   $$2m+17knw+O(k)=2m+O\bigl(n^2\lambda\log(n\lambda+2)\bigr).$$
--   3. The servers share $4k(nw+m2^{nw})$ Bell pairs, whose preparation does not depend on $F$. Each honest server performs $O(kmnw^24^{nw})$ operations, each a Hadamard, Pauli X, CNOT or Toffoli gate, a measurement of one qubit in the computational basis, or a classical bit operation. Both numbers are at most $m\cdot2^{O(n\log(n\lambda+2))}$.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: $\mathbb F_{2^w}$ with any fixed basis containing 1 (p.24) → the concrete field of App. C.2: first irreducible polynomial, polynomial basis, Fermat inverse, $\alpha_i$ the binary representation of $i$; reason: App. C.2 fixes this choice for the client; the multilinear extension is given by the standard formula of p.57
--   - encoding: each $O(\cdot)$ → one absolute real constant $C>0$ before $n,m,\lambda$; reason: the meaning of a uniform $O(\cdot)$; the arithmetic holds for all $n,m,\lambda\ge1$ (p.57)
--   - encoding: polynomial running time, memory, random bits; uniform; the same for every database; no oracle query → one machine in `TM2ComputableInPolyTime` for `clientStep` on an injective encoding with unary $n,m,\lambda$, a polynomial bound on the input length for every message in the alphabet, and a bound on `tapeLen`; reason: memory is at most input length plus time; `clientStep` has no database and no oracle in its type
--   - encoding: the communication of the honest execution → counted on every branch of nonzero trace of the honest execution; reason: these are the branches that occur
--   - encoding: the number of Bell pairs; their preparation does not depend on $F$ → `Fintype.card (BellIdx n m lam)`, and `bellVector` with no database in its type; reason: the qubits of the state are that index type (verified in the sanity file)
--   - encoding: an elementary operation → `ElemOp`: Hadamard, Pauli X, CNOT, Toffoli, measurement of one qubit, classical bit operation, each with at most one classical control cell, with ancillas returned to zero, and the outgoing message read from a fixed memory slot; reason: classical control is what A.1 and Claim C.3 describe, at constant overhead
--   - generalization: each honest server performs its operations for the database → one list of operations for all databases (`ServerImpl`), reading the tables as classical control from a memory computed by a bit-operation list from the truth table of $F$; reason: fixing $F$ gives a list for that database; the database is read-only classical control (A.1), and the proof (pp.57–58) counts the table computation
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.4, p.27; proof pp.57–58

import Definitions.Def_EntangledPIR_PrivateAgainstA
import Definitions.Def_EntangledPIR_ServerImpl
import Definitions.Def_EntangledPIR_encClientInput

namespace EntangledPIR

/-- **Lemma 5.4 (Communication and Resources)**, Mantri, manuscript (Nov. 2026), p.27. Let `n, m, λ ≥ 1`, let `k`, `w`,
`d = nw` be as in (5.1), and let `F` be a database. (i) The client of Protocol 1 is uniform and the same for every
database, and makes no oracle query. On every execution, for all messages of the servers, its running time, memory and
number of random bits are polynomial in `n, m, λ`. (ii) The protocol has a constant number of rounds. The answers of
honest servers contain `2m + 8knw` bits, and the total communication is `2m + 17knw + O(k) = 2m + O(n²λ log(nλ + 2))`
bits. (iii) The servers share `4k(nw + m 2^{nw})` Bell pairs, whose preparation does not depend on `F`. Each honest
server performs `O(k m n w² 4^{nw})` elementary operations. Both numbers are at most `m · 2^{O(n log(nλ+2))}`.

**Formalization Note.** Every `O(·)` is one absolute constant `C` before `n, m, λ`. (i): one machine in
`TM2ComputableInPolyTime` for `clientStep`, one function of `n, m, λ` in unary and with no database. The time bound is a
polynomial in the input length, and the input length is bounded by `q`, for all server messages in the alphabet. Memory
of a machine is at most input length plus time. The client model has no oracle. (ii): counted on every branch of positive
probability of the honest execution; the equality `= 2m + 17knw + O(k)` is the two-sided bound
`|comm − (2m + 17knw)| ≤ C k`. (iii): `bellVector` has no `F` in its type, and the implementation is `ServerImpl`. -/
theorem lemma_5_4 :
    ∃ (C : ℝ) (q : Polynomial ℕ), 0 < C ∧
      Nonempty (Turing.TM2ComputableInPolyTime encClientInput encClientOutput clientStep) ∧
      ∀ n m lam : ℕ, 1 ≤ n → 1 ≤ m → 1 ≤ lam →
        (tapeLen n lam ≤ q.eval (n + m + lam) ∧
          ∀ (x tape : List Bool) (srv : List (List Bool × List Bool)),
            x.length = n → tape.length = tapeLen n lam → srv.length ≤ numRounds →
            (∀ p ∈ srv, p.1.length ≤ msgBound n m lam ∧ p.2.length ≤ msgBound n m lam) →
            (encClientInput ⟨n, m, lam, x, tape, srv⟩).length ≤ q.eval (n + m + lam)) ∧
        ((numRounds : ℝ) ≤ C ∧
          ∀ (F : Bits n → Bits m) (x : Bits n) (tape : Bits (tapeLen n lam))
            (τ : Transcript (msgBound n m lam) numRounds),
            Matrix.trace (honestState lam F (List.ofFn x) (List.ofFn tape) numRounds τ) ≠ 0 →
            serverBits τ = 2 * m + 8 * shareCount n lam * (n * fieldWidth n lam) ∧
            (2 * m + 17 * shareCount n lam * (n * fieldWidth n lam) : ℝ) ≤
              ((commBits n m lam (List.ofFn x) (List.ofFn tape) τ : ℕ) : ℝ) + C * shareCount n lam ∧
            ((commBits n m lam (List.ofFn x) (List.ofFn tape) τ : ℕ) : ℝ) ≤
              2 * m + 17 * shareCount n lam * (n * fieldWidth n lam) + C * shareCount n lam ∧
            ((commBits n m lam (List.ofFn x) (List.ofFn tape) τ : ℕ) : ℝ) ≤
              2 * m + C * n ^ 2 * lam * Real.logb 2 (n * lam + 2)) ∧
        (Fintype.card (BellIdx n m lam) =
            4 * shareCount n lam * (n * fieldWidth n lam + m * 2 ^ (n * fieldWidth n lam)) ∧
          ((Fintype.card (BellIdx n m lam) : ℕ) : ℝ) ≤
            m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2)) ∧
          ∃ P : ServerImpl n m lam, P.Correct ∧
            ((P.opsA : ℕ) : ℝ) ≤
              C * shareCount n lam * m * n * (fieldWidth n lam : ℝ) ^ 2 * 4 ^ (n * fieldWidth n lam) ∧
            ((P.opsB : ℕ) : ℝ) ≤
              C * shareCount n lam * m * n * (fieldWidth n lam : ℝ) ^ 2 * 4 ^ (n * fieldWidth n lam) ∧
            ((P.opsA : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2)) ∧
            ((P.opsB : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ (C * n * Real.logb 2 (n * lam + 2))) := by sorry

end EntangledPIR
