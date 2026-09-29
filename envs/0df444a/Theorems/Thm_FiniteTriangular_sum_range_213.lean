-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_213
-- name    : FiniteTriangular.sum_range_213
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:32.663456+00:00
-- url     : https://prove2.me/theorems/f8363df4-f61c-4989-ba60-f60fc5ef4c30
-- title:
--   Sum of integers below 213
-- statement:
--   The sum of the nonnegative integers strictly less than $213$ equals $22578$. Equivalently, $\\sum_{k=0}^{213-1} k = 213(213-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_213 : ∑ k ∈ range 213, k = 22578 := by sorry

end FiniteTriangular
