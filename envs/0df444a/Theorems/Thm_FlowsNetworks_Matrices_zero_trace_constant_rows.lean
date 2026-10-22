-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_trace_constant_rows
-- name    : FlowsNetworks.Matrices.zero_trace_constant_rows
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:57.964894+00:00
-- url     : https://prove2.me/theorems/4b82921b-53c4-4b97-82f6-281972018a24
-- title:
--   Chapter II, Corollary 12.6 — zero-trace (0, 1)-matrices with all row-sum upper bounds equal
-- statement:
--   Let $a \ge 0$ be an integer and let $b_1 \ge b_2 \ge \dots \ge b_n$ be nonnegative integers. There is an $n \times n$ $(0, 1)$-matrix $(a_{ij})$ with
--   $$\sum_j a_{ij} \le a, \qquad \sum_i a_{ij} \ge b_j, \qquad \sum_i a_{ii} = 0$$
--   if and only if
--   $$\sum_{i=1}^n b_i \le n a \quad\text{and}\quad b_i \le n - 1 \quad (i = 1, \dots, n).$$
--
--   It is the case $a_i = a$ of Theorem 12.4: a loopless directed graph on $n$ nodes with out-degrees at most $a$ and in-degrees at least $b_i$ exists exactly when the total fits and no node asks for more than its $n - 1$ possible in-neighbours.
--
--   **Formalization Note** The ordering $b_1 \ge \dots \ge b_n$ (`Antitone b`) is the hypothesis of Theorem 12.4, which the corollary specializes (the book's proof uses it), and is carried here. `n - 1` is natural-number subtraction; at $n = 0$ there is no index $i$, so it is never evaluated. The matrix is a `Matrix (Fin n) (Fin n) ℕ` with entries at most $1$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 90, Corollary 12.6

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Corollary 12.6 (Ford–Fulkerson, *Flows in Networks*, p. 90). Let `a_i = a` for all
`i = 1, …, n`, with `a` a nonnegative integer, and let `b_1 ≥ b_2 ≥ ⋯ ≥ b_n` be nonnegative
integers (the hypothesis of Theorem 12.4, which the corollary specializes). There is an `n × n`
(0, 1)-matrix satisfying (12.20), `∑_j a_ij ≤ a`, `∑_i a_ij ≥ b_j` and `∑_i a_ii = 0`, if and only
if `∑_{i=1}^n b_i ≤ n a` and `b_i ≤ n − 1` for every `i`. -/
theorem zero_trace_constant_rows (n : ℕ) (a : ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ A : Matrix (Fin n) (Fin n) ℕ, IsZeroOne A ∧
        (∀ i, ∑ j, A i j ≤ a) ∧ (∀ j, b j ≤ ∑ i, A i j) ∧ ∑ i, A i i = 0) ↔
      (∑ i, b i ≤ n * a ∧ ∀ i, b i ≤ n - 1) := by sorry

end FlowsNetworks.Matrices
