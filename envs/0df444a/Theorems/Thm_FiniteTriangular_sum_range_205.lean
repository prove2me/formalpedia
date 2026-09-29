-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_205
-- name    : FiniteTriangular.sum_range_205
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:21.525212+00:00
-- url     : https://prove2.me/theorems/bf3db075-61f8-463d-a407-17131a27d6aa
-- title:
--   Sum of integers below 205
-- statement:
--   The sum of the nonnegative integers strictly less than $205$ equals $20910$. Equivalently, $\\sum_{k=0}^{205-1} k = 205(205-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_205 : ∑ k ∈ range 205, k = 20910 := by sorry

end FiniteTriangular
