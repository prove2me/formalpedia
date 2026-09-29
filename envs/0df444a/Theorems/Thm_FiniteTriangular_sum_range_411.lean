-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_411
-- name    : FiniteTriangular.sum_range_411
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:04.862877+00:00
-- url     : https://prove2.me/theorems/9b1def94-4a8b-47bb-aec3-64c90342de04
-- title:
--   Sum of integers below 411
-- statement:
--   The sum of the nonnegative integers strictly less than $411$ equals $84255$. Equivalently, $\\sum_{k=0}^{411-1} k = 411(411-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_411 : ∑ k ∈ range 411, k = 84255 := by sorry

end FiniteTriangular
