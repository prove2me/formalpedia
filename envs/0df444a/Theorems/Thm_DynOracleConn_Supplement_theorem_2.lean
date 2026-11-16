-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_2
-- name    : DynOracleConn.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:46:46.184362+00:00
-- url     : https://prove2.me/theorems/518bb895-ae6e-4298-a6bf-01220cc73d19
-- title:
--   Theorem 2, p.26 — incremental matrix model with $B\le cn/\log n$ bits: worst-case $\tilde\Omega(n^2/S)$ probes per update
-- statement:
--   There are constants $c,C>0$ and $k,n_0\in\mathbb N$ such that the following holds for all $n\ge n_0$, all $B$ with
--
--   $$1\le B\le \frac{cn}{\log_2 n},$$
--
--   all real $T$, all terminals $s\ne t$ in $[n]$, and every randomized algorithm for incremental dynamic $s$–$t$ connectivity in the adjacency-matrix model with at most $2^B$ persistent states. Suppose that the algorithm answers correctly after every update with probability at least $2/3$ on every insertion-only sequence, and that on every execution and every insertion-only sequence each update makes at most $T$ adjacency probes. Then
--
--   $$T\ \ge\ \frac{C\,n^2}{B\,(\log_2 n)^k}.$$
--
--   With $B=\Theta(S\log n)$ bits for $S$ words this is the paper's worst-case bound $\tilde\Omega(n^2/S)$ per update. It matches the worst-case time of the breadth-first-search algorithm of Theorem 1(a) for $\sqrt n\le S=O(n/\log^2n)$.
--
--   **Formalization Note** Each update's probes see the graph before it, and the answer is checked against the graph after it. Time is counted in oracle probes, which lower-bounds the time. Memory inside an update is not limited and the step may depend on the update index.
--
--   Differences from the source:
--   - reading: B = Θ(S log n) ≤ cn/log n; time Ω̃(n²/S) → the bound stated in B: T ≥ C·n²/(B·(log₂ n)^k), log base 2; reason: n²/S = Θ(n² log n / B), and Ω̃ absorbs the factor log n; the base of the logarithm is absorbed by c
--   - reading: Ω̃(·): factors polynomial in log n suppressed (footnote 1, p.1) → ∃ C > 0, k ∈ ℕ, n₀ with the bound divided by (log₂ n)^k for all n ≥ n₀; reason: the definition of Ω̃ with constants independent of n, B and the algorithm
--   - generalization: B bits of working memory (counting temporary storage) → a persistent state type with at most 2^B elements; memory inside an update is unlimited; the step may depend on the update index; reason: the base model of Theorem 4; it contains every B-bit algorithm of the paper, so a lower bound for it implies the printed one
--   - generalization: a randomized algorithm reading independent uniform random words → a probability space of deterministic algorithms; the tape is not charged as memory; reason: random tapes are one such space
--   - encoding: probabilities over the algorithm's randomness → measurable runs as a hypothesis; reason: a nondegeneracy condition: it makes the probability of correctness well defined on a general probability space
--   - encoding: worst-case time per update, on every execution (p.6) → at most T probes at every update of every insertion-only sequence, for every outcome of the randomness; reason: p.4: the lower bounds are proved for the number of queries, which never exceeds the time
--   - reading: B = Θ(S log n) bits, B = 0 not excluded → 1 ≤ B; reason: S ≥ 1 words gives B ≥ 1; the bound divides by B; at B = 0 the generalized model reads every pair in each update
--   - generalization: the algorithm's terminals s, t → every pair s ≠ t; reason: relabel the vertices of the hard instances; s = t is excluded because a constant answer is then correct
--   - encoding: [n]; B bits of state → Fin n; Fintype.card S ≤ 2^B; reason: Lean conventions; same instances
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 2, p.26 (also p.6)

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Incremental

namespace DynOracleConn

namespace Supplement

/-- **Theorem 2, p.26 (worst-case lower bound, matrix model).** Aryanfard, Henzinger, Kuszmaul,
Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 2, p.26 (also p.6): "There is a constant c > 0 such
that every randomized algorithm for Dynamic s-t Connectivity in the incremental setting and the matrix
model with B = Θ(S log n) ≤ cn/ log n bits of working memory such that, for every update sequence,
with probability at least 2/3, all of its answers are correct, needs worst-case time Ω̃(n²/S) per
update."

There are constants `c, C > 0` and `k, n₀ ∈ ℕ` such that for all `n ≥ n₀`, all `B` with
`1 ≤ B ≤ c·n / log₂ n`, all real `T`, all terminals `s ≠ t` and every state type with at most `2^B`
states: every randomized matrix-model algorithm with measurable runs that, on every insertion-only
sequence, answers correctly after every update with probability at least `2/3`, and that makes at most
`T` adjacency probes at every update of every insertion-only sequence on every execution, has
`T ≥ C·n² / (B·(log₂ n)^k)`.

**Formalization Note.**
1. The base model: `B` bits of persistent state are a state type with at most `2^B` elements; memory
   inside an update is not limited; the step may depend on the update index; randomness is a
   probability space of deterministic algorithms with measurable runs.
2. `Ω̃(n²/S)` with `B = Θ(S log n)`: since `n²/S = Θ(n² log n / B)` and `Ω̃` suppresses factors
   polynomial in `log n` (footnote 1, p.1), the bound is `C·n²/(B·(log₂ n)^k)` with `C, k` fixed with
   `c`, for all large `n`.
3. Worst-case time is counted in oracle probes (p.4: "We prove our lower bounds for the number of
   queries"), on every execution (p.6). Snapshot semantics as in the base model. -/
theorem theorem_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k n₀ : ℕ,
      ∀ (n B : ℕ) (T : ℝ), n₀ ≤ n → 1 ≤ B → (B : ℝ) ≤ c * n / Real.logb 2 n →
      ∀ s t : Fin n, s ≠ t →
      ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B →
      ∀ A : RandAlg n (Fin n × Fin n) Bool S, MeasurableRuns A matrixOracle →
        (∀ σ : List (PunctSketch.Update n), IsIncremental σ →
          (2 / 3 : ENNReal) ≤ A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ}) →
        WorstCaseOn A matrixOracle IsIncremental T →
        C * (n : ℝ) ^ 2 / ((B : ℝ) * Real.logb 2 n ^ k) ≤ T := by sorry

end Supplement

end DynOracleConn
