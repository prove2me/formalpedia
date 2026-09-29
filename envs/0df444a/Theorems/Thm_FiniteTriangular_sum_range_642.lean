-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_642
-- name    : FiniteTriangular.sum_range_642
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:12.679119+00:00
-- url     : https://prove2.me/theorems/b393747a-6310-4364-916d-25b8b4dba7b9
-- title:
--   Sum of integers below 642
-- statement:
--   The sum of the nonnegative integers strictly less than $642$ equals $205761$. Equivalently, $\\sum_{k=0}^{642-1} k = 642(642-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_642 : ∑ k ∈ range 642, k = 205761 := by sorry

end FiniteTriangular
