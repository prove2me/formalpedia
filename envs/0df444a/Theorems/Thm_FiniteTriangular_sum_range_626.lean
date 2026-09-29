-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_626
-- name    : FiniteTriangular.sum_range_626
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:50.464718+00:00
-- url     : https://prove2.me/theorems/721d2b14-6d70-4274-a0a8-354e7096e9e1
-- title:
--   Sum of integers below 626
-- statement:
--   The sum of the nonnegative integers strictly less than $626$ equals $195625$. Equivalently, $\\sum_{k=0}^{626-1} k = 626(626-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_626 : ∑ k ∈ range 626, k = 195625 := by sorry

end FiniteTriangular
