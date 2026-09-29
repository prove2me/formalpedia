-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_430
-- name    : FiniteTriangular.sum_range_430
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:37.736592+00:00
-- url     : https://prove2.me/theorems/9c21bb0e-8ce6-43f9-8ae5-25f289abd231
-- title:
--   Sum of integers below 430
-- statement:
--   The sum of the nonnegative integers strictly less than $430$ equals $92235$. Equivalently, $\\sum_{k=0}^{430-1} k = 430(430-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_430 : ∑ k ∈ range 430, k = 92235 := by sorry

end FiniteTriangular
