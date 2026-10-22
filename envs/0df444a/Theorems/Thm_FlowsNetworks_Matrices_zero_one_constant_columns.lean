-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_one_constant_columns
-- name    : FlowsNetworks.Matrices.zero_one_constant_columns
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:08.690588+00:00
-- url     : https://prove2.me/theorems/bf20b99c-b51b-419c-a398-e22b59d3c70b
-- title:
--   Chapter II, Corollary 12.2 — (0, 1)-matrices with all column-sum lower bounds equal
-- statement:
--   Let $a_1, \dots, a_m$ be nonnegative integers with conjugate sequence $a^*_j = |\{\, i \mid a_i \ge j \,\}|$, and let $b \ge 0$ be an integer. There is an $m \times n$ $(0, 1)$-matrix $A = (a_{ij})$ with
--   $$\sum_i a_{ij} \ge b \quad (j = 1, \dots, n), \qquad \sum_j a_{ij} \le a_i \quad (i = 1, \dots, m)$$
--   if and only if
--   $$n b \le \sum_{j=1}^n a^*_j.$$
--
--   It is the case $b_j = b$ of Theorem 12.1: with equal column requirements only the total condition $k = n$ matters.
--
--   **Formalization Note** The matrix is a `Matrix (Fin m) (Fin n) ℕ` with entries at most $1$; $b$ and the $a_i$ are natural numbers.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 80, Corollary 12.2

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Corollary 12.2 (Ford–Fulkerson, *Flows in Networks*, p. 80). Let `a_1, …, a_m` be
nonnegative integers and let `b_j = b` for all `j = 1, …, n`, with `b` a nonnegative integer.
There is an `m × n` (0, 1)-matrix satisfying (12.7), `∑_i a_ij ≥ b` and `∑_j a_ij ≤ a_i`, if and
only if `n b ≤ ∑_{j=1}^n a*_j`. -/
theorem zero_one_constant_columns (m n : ℕ) (a : Fin m → ℕ) (b : ℕ) :
    (∃ A : Matrix (Fin m) (Fin n) ℕ, IsZeroOne A ∧
        (∀ j, b ≤ ∑ i, A i j) ∧ (∀ i, ∑ j, A i j ≤ a i)) ↔
      n * b ≤ ∑ j : Fin n, conj a j := by sorry

end FlowsNetworks.Matrices
