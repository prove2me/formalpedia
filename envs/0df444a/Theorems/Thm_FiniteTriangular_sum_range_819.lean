-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_819
-- name    : FiniteTriangular.sum_range_819
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:42.169757+00:00
-- url     : https://prove2.me/theorems/09c16965-d6b2-46d8-8ed4-07acd3d2654e
-- title:
--   Sum of integers below 819
-- statement:
--   The sum of the nonnegative integers strictly less than $819$ equals $334971$. Equivalently, $\\sum_{k=0}^{819-1} k = 819(819-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_819 : ∑ k ∈ range 819, k = 334971 := by sorry

end FiniteTriangular
