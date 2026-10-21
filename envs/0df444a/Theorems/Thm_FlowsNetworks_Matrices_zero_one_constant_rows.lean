-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_zero_one_constant_rows
-- name    : FlowsNetworks.Matrices.zero_one_constant_rows
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:53.554739+00:00
-- url     : https://prove2.me/theorems/7f4b8398-af82-4995-a2e6-25706595b89c
-- title:
--   Chapter II, Corollary 12.3 — (0, 1)-matrices with all row-sum upper bounds equal
-- statement:
--   Let $a \ge 0$ be an integer and let $b_1 \ge b_2 \ge \dots \ge b_n$ be nonnegative integers. There is an $m \times n$ $(0, 1)$-matrix $A = (a_{ij})$ with
--   $$\sum_i a_{ij} \ge b_j \quad (j = 1, \dots, n), \qquad \sum_j a_{ij} \le a \quad (i = 1, \dots, m)$$
--   if and only if
--   $$\sum_{j=1}^n b_j \le m a \quad\text{and}\quad b_j \le m \quad (j = 1, \dots, n).$$
--
--   It is the case $a_i = a$ of Theorem 12.1. In the seating language of the book: $n$ families of sizes $b_j$ can be seated at $m$ tables of $a$ seats each, no two members of a family at one table, exactly when the seats suffice and no family is larger than the number of tables.
--
--   **Formalization Note** The ordering $b_1 \ge \dots \ge b_n$ (`Antitone b`) is the standing hypothesis of Theorem 12.1, of which the book states this as a consequence, and is carried here; the condition itself does not depend on the order of the $b_j$. The matrix is a `Matrix (Fin m) (Fin n) ℕ` with entries at most $1$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 80, Corollary 12.3

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_ZeroOne

namespace FlowsNetworks.Matrices

/-- Chapter II, Corollary 12.3 (Ford–Fulkerson, *Flows in Networks*, p. 80). Let `a_i = a` for all
`i = 1, …, m`, with `a` a nonnegative integer, and let `b_1 ≥ b_2 ≥ ⋯ ≥ b_n` be nonnegative
integers (the standing hypothesis of Theorem 12.1, of which this is a consequence). There is an
`m × n` (0, 1)-matrix satisfying (12.7), `∑_i a_ij ≥ b_j` and `∑_j a_ij ≤ a`, if and only if
`∑_{j=1}^n b_j ≤ m a` and `b_j ≤ m` for every `j`. -/
theorem zero_one_constant_rows (m n : ℕ) (a : ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ A : Matrix (Fin m) (Fin n) ℕ, IsZeroOne A ∧
        (∀ j, b j ≤ ∑ i, A i j) ∧ (∀ i, ∑ j, A i j ≤ a)) ↔
      (∑ j, b j ≤ m * a ∧ ∀ j, b j ≤ m) := by sorry

end FlowsNetworks.Matrices
