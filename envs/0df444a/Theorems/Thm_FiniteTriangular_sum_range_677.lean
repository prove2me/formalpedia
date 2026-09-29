-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_677
-- name    : FiniteTriangular.sum_range_677
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:57.954034+00:00
-- url     : https://prove2.me/theorems/07bf1670-4ca4-4a0a-8ec5-0c8ad65e20d5
-- title:
--   Sum of integers below 677
-- statement:
--   The sum of the nonnegative integers strictly less than $677$ equals $228826$. Equivalently, $\\sum_{k=0}^{677-1} k = 677(677-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_677 : ∑ k ∈ range 677, k = 228826 := by sorry

end FiniteTriangular
