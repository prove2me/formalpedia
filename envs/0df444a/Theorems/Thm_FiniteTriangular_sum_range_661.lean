-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_661
-- name    : FiniteTriangular.sum_range_661
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:37.012185+00:00
-- url     : https://prove2.me/theorems/29930282-34e9-4105-95b2-2d9520011e60
-- title:
--   Sum of integers below 661
-- statement:
--   The sum of the nonnegative integers strictly less than $661$ equals $218130$. Equivalently, $\\sum_{k=0}^{661-1} k = 661(661-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_661 : ∑ k ∈ range 661, k = 218130 := by sorry

end FiniteTriangular
