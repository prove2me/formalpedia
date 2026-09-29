-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_468
-- name    : FiniteTriangular.sum_range_468
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:44.644654+00:00
-- url     : https://prove2.me/theorems/43c73aa3-3142-438f-a7c1-2586197ae722
-- title:
--   Sum of integers below 468
-- statement:
--   The sum of the nonnegative integers strictly less than $468$ equals $109278$. Equivalently, $\\sum_{k=0}^{468-1} k = 468(468-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_468 : ∑ k ∈ range 468, k = 109278 := by sorry

end FiniteTriangular
