-- Prove2me | Theorems.Thm_Conway99_ten_of_no_four_diag_count
-- name    : Conway99.ten_of_no_four_diag_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-08T00:23:58.428889+00:00
-- url     : https://prove2.me/theorems/d17dc197-a380-4842-bf0d-0125180621a9
-- title:
--   Diagonal census for the trace-$10$ no-four orbit-matrix case
-- statement:
--   Let $C$ be a $9\times 9$ matrix over $\mathbb{N}$ whose diagonal entries lie in $\{0,2,4\}$, whose diagonal sums to $10$, and with no diagonal entry equal to $4$. Then exactly five diagonal entries equal $2$ and four equal $0$. Indeed every diagonal entry is $0$ or $2$, so with $c_2$ entries equal to $2$ the trace condition gives $2c_2 = 10$ and the nine diagonal positions give $c_2 + c_0 = 9$. This pins the row-type multiset used by the profile census in the trace-$10$, no-four branch of Wilbrink's Theorem 5.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', EUT Report 84-WSK-03, 1984, Theorem 5, pp. 350-354, https://pure.tue.nl/ws/files/2449333/256699.pdf ; diagonal census for the trace-10, no-four branch.

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Conway99

theorem ten_of_no_four_diag_count
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : ∑ i, C i i = 10)
    (hfour : ∀ i, C i i ≠ 4) :
    (Finset.univ.filter (fun i => C i i = 2)).card = 5 ∧
    (Finset.univ.filter (fun i => C i i = 0)).card = 4 := by sorry

end Conway99
