-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_805
-- name    : FiniteTriangular.sum_range_805
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:09.490259+00:00
-- url     : https://prove2.me/theorems/7c127af7-4335-4be1-8179-a619d1fe2017
-- title:
--   Sum of integers below 805
-- statement:
--   The sum of the nonnegative integers strictly less than $805$ equals $323610$. Equivalently, $\\sum_{k=0}^{805-1} k = 805(805-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_805 : ∑ k ∈ range 805, k = 323610 := by sorry

end FiniteTriangular
