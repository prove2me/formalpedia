-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_610
-- name    : FiniteTriangular.sum_range_610
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:29.691778+00:00
-- url     : https://prove2.me/theorems/8c5d9a78-7caa-41df-87d6-93c409203fed
-- title:
--   Sum of integers below 610
-- statement:
--   The sum of the nonnegative integers strictly less than $610$ equals $185745$. Equivalently, $\\sum_{k=0}^{610-1} k = 610(610-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_610 : ∑ k ∈ range 610, k = 185745 := by sorry

end FiniteTriangular
