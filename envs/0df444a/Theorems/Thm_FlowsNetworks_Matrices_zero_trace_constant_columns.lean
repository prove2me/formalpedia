-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_trace_constant_columns
-- name    : FlowsNetworks.Matrices.zero_trace_constant_columns
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:00.280737+00:00
-- url     : https://prove2.me/theorems/1e071fba-392b-4698-a368-a54ee76ff2ef
-- title:
--   Chapter II, Corollary 12.5 — zero-trace (0, 1)-matrices with all column-sum lower bounds equal
-- statement:
--   Let $a_1 \ge a_2 \ge \dots \ge a_n$ be nonnegative integers with diagonally restricted conjugate $(a^{**}_k)$, and let $b \ge 0$ be an integer. There is an $n \times n$ $(0, 1)$-matrix $(a_{ij})$ with
--   $$\sum_j a_{ij} \le a_i, \qquad \sum_i a_{ij} \ge b, \qquad \sum_i a_{ii} = 0$$
--   if and only if
--   $$n b \le \sum_{i=1}^n a^{**}_i.$$
--
--   It is the case $b_i = b$ of Theorem 12.4. Although $(a^{**}_k)$ need not be monotone, only the total condition $k = n$ matters here.
--
--   **Formalization Note** The ordering $a_1 \ge \dots \ge a_n$ (`Antitone a`) is the hypothesis of Theorem 12.4, which the corollary specializes, and is carried here. The matrix is a `Matrix (Fin n) (Fin n) ℕ` with entries at most $1$, and zero trace is $\sum_i a_{ii} = 0$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 90, Corollary 12.5

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Corollary 12.5 (Ford–Fulkerson, *Flows in Networks*, p. 90). Let
`a_1 ≥ a_2 ≥ ⋯ ≥ a_n` be nonnegative integers (the hypothesis of Theorem 12.4, which the
corollary specializes) and let `b_i = b` for all `i = 1, …, n`, with `b` a nonnegative integer.
There is an `n × n` (0, 1)-matrix satisfying (12.20), `∑_j a_ij ≤ a_i`, `∑_i a_ij ≥ b` and
`∑_i a_ii = 0`, if and only if `n b ≤ ∑_{i=1}^n a**_i`. -/
theorem zero_trace_constant_columns (n : ℕ) (a : Fin n → ℕ) (ha : Antitone a) (b : ℕ) :
    (∃ A : Matrix (Fin n) (Fin n) ℕ, IsZeroOne A ∧
        (∀ i, ∑ j, A i j ≤ a i) ∧ (∀ j, b ≤ ∑ i, A i j) ∧ ∑ i, A i i = 0) ↔
      n * b ≤ ∑ i : Fin n, diagConj a i := by sorry

end FlowsNetworks.Matrices
