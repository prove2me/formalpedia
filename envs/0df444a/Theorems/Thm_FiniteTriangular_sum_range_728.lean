-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_728
-- name    : FiniteTriangular.sum_range_728
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:45.807291+00:00
-- url     : https://prove2.me/theorems/43803837-5eae-4ef3-a1ea-09fbd65d65df
-- title:
--   Sum of integers below 728
-- statement:
--   The sum of the nonnegative integers strictly less than $728$ equals $264628$. Equivalently, $\\sum_{k=0}^{728-1} k = 728(728-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_728 : ∑ k ∈ range 728, k = 264628 := by sorry

end FiniteTriangular
