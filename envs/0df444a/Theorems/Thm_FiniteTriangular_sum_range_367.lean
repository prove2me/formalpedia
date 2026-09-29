-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_367
-- name    : FiniteTriangular.sum_range_367
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:13.727598+00:00
-- url     : https://prove2.me/theorems/d8f56acb-3bcd-4f95-9c9b-ed64ba4dd8c0
-- title:
--   Sum of integers below 367
-- statement:
--   The sum of the nonnegative integers strictly less than $367$ equals $67161$. Equivalently, $\\sum_{k=0}^{367-1} k = 367(367-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_367 : ∑ k ∈ range 367, k = 67161 := by sorry

end FiniteTriangular
