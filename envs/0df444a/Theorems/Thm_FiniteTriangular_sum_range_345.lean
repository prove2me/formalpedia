-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_345
-- name    : FiniteTriangular.sum_range_345
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:37.832185+00:00
-- url     : https://prove2.me/theorems/4d5c7e5a-cfa4-40a7-8fc3-5aedc1167ea5
-- title:
--   Sum of integers below 345
-- statement:
--   The sum of the nonnegative integers strictly less than $345$ equals $59340$. Equivalently, $\\sum_{k=0}^{345-1} k = 345(345-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_345 : ∑ k ∈ range 345, k = 59340 := by sorry

end FiniteTriangular
