-- Prove2me | Theorems.Thm_DynConnWC_theorem_1
-- name    : DynConnWC.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:41.837227+00:00
-- url     : https://prove2.me/theorems/c74291f8-e028-4ef0-b841-789181451660
-- title:
--   Theorem 1 — $O(\log^3n)$ worst-case updates, $O(\log n/\log\log n)$ queries, $O(n\log^2n)$ words, correct w.p. $1-n^{-\beta}$
-- statement:
--   Fix $d,\beta>0$. There are two programs $P,P_d$ of the online randomized word RAM and constants $C,c_0$, depending only on $d$ and $\beta$, such that for all $n\ge2$ and word sizes $W\ge c_0\lceil\log_2n\rceil$, the following hold for fully dynamic connectivity on $n$ vertices starting from the empty graph.
--
--   1. **Time, always.** For both programs, on every tape and every valid sequence of operations of any length: every read is reached and every query is answered with $0$ or $1$; initialization takes at most $Cn\log_2^2n$ steps, each update at most $C\log_2^3n$, and each query at most $C\max(1,\log_2n/\log_2\log_2n)$.
--   2. **Space.** On every tape and valid sequence, $P$ touches only memory cells below $Cn\log_2^2n$. $P_d$ touches only cells below $Cn\log_2^2n$ during initialization and below $C(m_t+n\log_2^2n)$ during operation $t$.
--   3. **Correctness.** For both programs, and every valid sequence with at most $\lceil n^d\rceil$ updates and any number of queries, fixed in advance, all query answers are correct with probability at least $1-n^{-\beta}$ over the tape.
--   4. **Adaptivity.** The same bound holds, for both programs, when the sequence is chosen by an adversary that sees the previous answers but not the tape or memory.
--   5. **Dictionary.** Every positive answer of $P_d$ is correct on every tape and every valid sequence.
--
--   It improves the $O(\log^4n)$ worst-case update time of Gibb, Kapron, King and Thorn, and Wang's $O(\log^4n)$ for deletions, to $O(\log^3n)$ for both insertions and deletions, with the same space.
--
--   Differences from the source:
--   - generalization: words of $\Theta(\log n)$ bits → every $W\ge c_0\lceil\log_2n\rceil$; reason: a program that works for all larger $W$ specializes to the source's word size
--   - encoding: a word RAM with randomness → the machine of `Def_DynConnWC_Program`: unit-cost arithmetic and bit operations, indirect access, and a tape of independent uniform words; reason: the source fixes the word size and the cost measure and names no instruction list
--   - encoding: a data structure taking operations → input words read one at a time; time counted between reads; a query's answer is the first word written in its window; reason: this makes worst-case time per online operation a statement about one run
--   - reading: $O(n\log^2n)$ and $O(m+n\log^2n)$ words → bounds on the memory cells touched, with $m_t$ the edge count after operation $t$; reason: space in words is measured by the addresses used, and this is the stronger reading (current $m$)
--   - reading: these bounds always hold → on every tape and every valid sequence of any length; reason: nothing in the algorithm depends on the update count (p.17, p.24)
--   - reading: an adversary that sees the previous query answers → deterministic strategies on the history, with validity and the update count required of the run against the exact oracle; reason: the proof of Lemma 25 fixes the adversary's randomness, averages, and applies the condition to that run; a uniform bound covers mixtures
--   - encoding: any number of queries → every finite number $N$ of rounds, with the bound uniform in $N$; reason: by continuity of measure this is equivalent to the infinite run
--   - encoding: $O(\log n/\log\log n)$ query time → $C\max(1,\log_2n/\log_2\log_2n)$; reason: $\log_2\log_22=0$, and Lean's division by zero would give $0$ at $n=2$; the maximum is inert for $n\ge4$
--   - encoding: a yes/no answer to each query → the answer word is $0$ or $1$, on every tape and every valid sequence (clause 1); reason: the data structure always answers yes or no; this clause fixes the word encoding of that answer and adds no content beyond it
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 1, p.1 (PDF 2); §2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_DynConnWC_Bounds

set_option autoImplicit false

namespace DynConnWC

/-- **Theorem 1.** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.1 (PDF 2).
"Fix constants d, β > 0. There is a randomized data structure for fully dynamic connectivity on n
vertices, starting from the empty graph, with O(log³ n) worst-case update time, O(log n/ log log n)
worst-case query time, O(n log² n) words of space, and O(n log² n) initialization time. These bounds
always hold, and the hidden constants depend only on d and β. For every sequence of at most ⌈n^d⌉
updates, interleaved with any number of queries, all query answers are correct with probability at
least 1 − n^{−β}. This also holds when the sequence is chosen by an adversary that sees the previous
query answers, but not the algorithm's randomness or the internal state. With an additional dictionary
of the current edges, the space is O(m + n log² n) words, the time bounds are unchanged, and every
positive query answer is correct regardless of the random choices."

**Formalization Note.** `P` is the plain structure and `Pd` the one with the dictionary, both programs
of the online randomized word RAM of `Def_DynConnWC_Program`. The programs and `C, c₀` are chosen after
`d, β` and before `n, W`. Words have `W ≥ c₀⌈log₂ n⌉` bits, an instruction costs one step, and the input
arrives one word per `read`. The resource bounds hold on every tape and every valid sequence of any
length; correctness is over the tape, for fixed sequences and for adversaries that see only the answers. -/
theorem theorem_1 (d β : ℝ) (hd : 0 < d) (hβ : 0 < β) :
    ∃ (P Pd : Program) (C c₀ : ℕ), ∀ n, 2 ≤ n → ∀ W, c₀ * Nat.clog 2 n ≤ W →
      (∀ Q ∈ [P, Pd], ∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ → TimeBounds C W Q n ω σ) ∧
      (∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ → SpaceBound C W P n ω σ) ∧
      (∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ → DictSpaceBound C W Pd n ω σ) ∧
      (∀ Q ∈ [P, Pd], ∀ σ : List (Op n), Valid σ → numUpdates σ ≤ T0par n d →
        ENNReal.ofReal (1 - deltaPar n β) ≤ tapeLaw W {ω | AllCorrect W Q n ω σ}) ∧
      (∀ Q ∈ [P, Pd], ∀ A : Adversary n,
        (∀ N, Valid (oracleOps A N) ∧ numUpdates (oracleOps A N) ≤ T0par n d) →
        ∀ N, ENNReal.ofReal (1 - deltaPar n β) ≤ tapeLaw W {ω | AdvAllCorrect W Q A N ω}) ∧
      (∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ → PositiveCorrect W Pd n ω σ) := by sorry

end DynConnWC
