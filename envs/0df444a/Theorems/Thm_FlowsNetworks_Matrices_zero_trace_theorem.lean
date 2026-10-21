-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_trace_theorem
-- name    : FlowsNetworks.Matrices.zero_trace_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:55.375559+00:00
-- url     : https://prove2.me/theorems/de29c1c0-4e2a-4220-a474-63c675c72306
-- title:
--   Chapter II, Theorem 12.4 — (0, 1)-matrices with zero trace and bounded row and column sums
-- statement:
--   Let $a_1 \ge a_2 \ge \dots \ge a_n$ and $b_1 \ge b_2 \ge \dots \ge b_n$ be nonnegative integers, and let $(a^{**}_k)$ be the diagonally restricted conjugate of $(a_i)$: in an $n \times n$ array, row $i$ places $a_i$ dots in its leftmost columns other than column $i$ (all $n - 1$ of them if $a_i \ge n - 1$), and $a^{**}_k$ is the number of dots in column $k$, that is,
--   $$a^{**}_k = |\{\, i \mid i < k,\ a_i \ge k - 1 \,\}| + |\{\, i \mid i > k,\ a_i \ge k \,\}|.$$
--   There is an $n \times n$ $(0, 1)$-matrix $(a_{ij})$ with
--   $$\sum_j a_{ij} \le a_i, \qquad \sum_i a_{ij} \ge b_j, \qquad \sum_i a_{ii} = 0$$
--   if and only if
--   $$\sum_{i=1}^k b_i \le \sum_{i=1}^k a^{**}_i, \qquad k = 1, \dots, n.$$
--
--   Read as a directed graph on $n$ nodes, with an arc from $i$ to $j$ for every entry $a_{ij} = 1$, the theorem decides when there is a loopless directed graph whose out-degrees are at most $a_i$ and whose in-degrees are at least $b_j$. It is the zero-trace analogue of the Gale–Ryser theorem (Theorem 12.1), with the conjugate sequence replaced by the diagonally restricted one.
--
--   **Formalization Note** The matrix is a `Matrix (Fin n) (Fin n) ℕ` with entries at most $1$, and zero trace is literally $\sum_i a_{ii} = 0$; over $\mathbb N$ this forces every diagonal entry to be $0$. Indices start at $0$: the book's index $i$ is `i + 1`, and $\sum_{i=1}^k$ runs over `i.val < k`. Both orderings are hypotheses (`Antitone a`, `Antitone b`). $a^{**}$ is the explicit count `diagConj`, not defined through matrices, and the condition is required for every $k = 1, \dots, n$, not only for $k = n$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 89, Theorem 12.4 (statement continues on p. 90)

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Theorem 12.4 (Ford–Fulkerson, *Flows in Networks*, p. 89). Let
`a_1 ≥ a_2 ≥ ⋯ ≥ a_n` and `b_1 ≥ b_2 ≥ ⋯ ≥ b_n` be nonnegative integers. There is an `n × n`
(0, 1)-matrix `(a_ij)` with `∑_j a_ij ≤ a_i`, `∑_i a_ij ≥ b_j` and `∑_i a_ii = 0` (12.20) if and
only if `∑_{i=1}^k b_i ≤ ∑_{i=1}^k a**_i` for `k = 1, …, n` (12.21), where `(a**_i)` is the
diagonally restricted conjugate of `(a_i)`. Indices are 0-based: the book's `i` is `i + 1`. -/
theorem zero_trace_theorem (n : ℕ) (a b : Fin n → ℕ) (ha : Antitone a) (hb : Antitone b) :
    (∃ A : Matrix (Fin n) (Fin n) ℕ, IsZeroOne A ∧
        (∀ i, ∑ j, A i j ≤ a i) ∧ (∀ j, b j ≤ ∑ i, A i j) ∧ ∑ i, A i i = 0) ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∑ i : Fin n with i.val < k, b i ≤ ∑ i : Fin n with i.val < k, diagConj a i := by sorry

end FlowsNetworks.Matrices
