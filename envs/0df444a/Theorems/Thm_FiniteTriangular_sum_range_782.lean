-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_782
-- name    : FiniteTriangular.sum_range_782
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:15.474762+00:00
-- url     : https://prove2.me/theorems/bd620f83-46c5-4485-a846-75b373c46ec8
-- title:
--   Sum of integers below 782
-- statement:
--   The sum of the nonnegative integers strictly less than $782$ equals $305371$. Equivalently, $\\sum_{k=0}^{782-1} k = 782(782-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_782 : ∑ k ∈ range 782, k = 305371 := by sorry

end FiniteTriangular
