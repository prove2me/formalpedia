-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_326
-- name    : FiniteTriangular.sum_range_326
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:12.758934+00:00
-- url     : https://prove2.me/theorems/21958811-cc54-4bcb-b496-28c9dc44a696
-- title:
--   Sum of integers below 326
-- statement:
--   The sum of the nonnegative integers strictly less than $326$ equals $52975$. Equivalently, $\\sum_{k=0}^{326-1} k = 326(326-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_326 : ∑ k ∈ range 326, k = 52975 := by sorry

end FiniteTriangular
