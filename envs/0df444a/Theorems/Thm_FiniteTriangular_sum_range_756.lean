-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_756
-- name    : FiniteTriangular.sum_range_756
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:56.402887+00:00
-- url     : https://prove2.me/theorems/86ad2af2-e014-4ddd-934e-772c97d43f61
-- title:
--   Sum of integers below 756
-- statement:
--   The sum of the nonnegative integers strictly less than $756$ equals $285390$. Equivalently, $\\sum_{k=0}^{756-1} k = 756(756-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_756 : ∑ k ∈ range 756, k = 285390 := by sorry

end FiniteTriangular
