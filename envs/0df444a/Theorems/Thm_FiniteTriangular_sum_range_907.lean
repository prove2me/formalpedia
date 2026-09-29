-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_907
-- name    : FiniteTriangular.sum_range_907
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:12.412259+00:00
-- url     : https://prove2.me/theorems/4ed17f92-1401-497d-bef6-4c1258b160d4
-- title:
--   Sum of integers below 907
-- statement:
--   The sum of the nonnegative integers strictly less than $907$ equals $410871$. Equivalently, $\\sum_{k=0}^{907-1} k = 907(907-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_907 : ∑ k ∈ range 907, k = 410871 := by sorry

end FiniteTriangular
