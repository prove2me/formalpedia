-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_917
-- name    : FiniteTriangular.sum_range_917
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:47.719387+00:00
-- url     : https://prove2.me/theorems/3b61ac0e-6d21-4b3a-9950-868b37236258
-- title:
--   Sum of integers below 917
-- statement:
--   The sum of the nonnegative integers strictly less than $917$ equals $419986$. Equivalently, $\\sum_{k=0}^{917-1} k = 917(917-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_917 : ∑ k ∈ range 917, k = 419986 := by sorry

end FiniteTriangular
