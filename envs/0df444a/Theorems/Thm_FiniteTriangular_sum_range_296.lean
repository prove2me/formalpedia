-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_296
-- name    : FiniteTriangular.sum_range_296
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:06.685667+00:00
-- url     : https://prove2.me/theorems/d9f35cf3-577b-4a70-b522-e67db48f64b0
-- title:
--   Sum of integers below 296
-- statement:
--   The sum of the nonnegative integers strictly less than $296$ equals $43660$. Equivalently, $\\sum_{k=0}^{296-1} k = 296(296-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_296 : ∑ k ∈ range 296, k = 43660 := by sorry

end FiniteTriangular
