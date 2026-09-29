-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_366
-- name    : FiniteTriangular.sum_range_366
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:15.224253+00:00
-- url     : https://prove2.me/theorems/cbc8272b-785b-4bdd-81d4-36368f51e58f
-- title:
--   Sum of integers below 366
-- statement:
--   The sum of the nonnegative integers strictly less than $366$ equals $66795$. Equivalently, $\\sum_{k=0}^{366-1} k = 366(366-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_366 : ∑ k ∈ range 366, k = 66795 := by sorry

end FiniteTriangular
