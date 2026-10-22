-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_one_matrix_existence
-- name    : FlowsNetworks.Matrices.zero_one_matrix_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:58.994612+00:00
-- url     : https://prove2.me/theorems/b28170b6-9385-47ad-a81b-05e5452964bd
-- title:
--   Chapter II, Theorem 12.1 — (0, 1)-matrices with column sums at least $b_j$ and row sums at most $a_i$
-- statement:
--   Let $a_1, \dots, a_m$ and $b_1, \dots, b_n$ be nonnegative integers with
--   $$b_1 \ge b_2 \ge \dots \ge b_n,$$
--   and let $a^*_j = |\{\, i \mid a_i \ge j \,\}|$ be the conjugate sequence of $(a_i)$. There is an $m \times n$ $(0, 1)$-matrix $A = (a_{ij})$ with
--   $$\sum_i a_{ij} \ge b_j \quad (j = 1, \dots, n), \qquad \sum_j a_{ij} \le a_i \quad (i = 1, \dots, m)$$
--   if and only if
--   $$\sum_{j=1}^k b_j \le \sum_{j=1}^k a^*_j, \qquad k = 1, \dots, n.$$
--
--   This is the Gale–Ryser theorem in inequality form: the row sums are bounded above and the column sums below, the totals $\sum_i a_i$ and $\sum_j b_j$ need not agree, the $a_i$ need not be sorted, and zeros are allowed. When the bounds hold with equality it characterizes the margins of $(0, 1)$-matrices, i.e. the degree sequences of bipartite graphs.
--
--   **Formalization Note** The matrix is a `Matrix (Fin m) (Fin n) ℕ` with entries at most $1$; indices start at $0$, so the partial sum $\sum_{j=1}^k$ runs over the columns `j` with `j.val < k`. "$b_1 \ge \dots \ge b_n$" is `Antitone b`; the $a_i$ are unconstrained natural numbers. The condition is required for every $k = 1, \dots, n$, not only for $k = n$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 79–80, Theorem 12.1

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Theorem 12.1 (Gale, Ryser; Ford–Fulkerson, *Flows in Networks*, pp. 79–80). Let
`a_i` (`i = 1, …, m`) and `b_j` (`j = 1, …, n`) be nonnegative integers with
`b_1 ≥ b_2 ≥ ⋯ ≥ b_n`. There is an `m × n` (0, 1)-matrix `A = (a_ij)` with
`∑_i a_ij ≥ b_j` and `∑_j a_ij ≤ a_i` (12.7) if and only if
`∑_{j=1}^k b_j ≤ ∑_{j=1}^k a*_j` for `k = 1, …, n` (12.8), where `a*_j = |{i | a_i ≥ j}|`.
Indices are 0-based: the book's `j` is `j + 1`, and `∑_{j=1}^k` is the sum over `j.val < k`. -/
theorem zero_one_matrix_existence (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ A : Matrix (Fin m) (Fin n) ℕ, IsZeroOne A ∧
        (∀ j, b j ≤ ∑ i, A i j) ∧ (∀ i, ∑ j, A i j ≤ a i)) ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∑ j : Fin n with j.val < k, b j ≤ ∑ j : Fin n with j.val < k, conj a j := by sorry

end FlowsNetworks.Matrices
