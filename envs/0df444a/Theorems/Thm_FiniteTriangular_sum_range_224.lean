-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_224
-- name    : FiniteTriangular.sum_range_224
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:17.63201+00:00
-- url     : https://prove2.me/theorems/a389b668-c4b7-4055-9e1c-8a27df364f77
-- title:
--   Sum of integers below 224
-- statement:
--   The sum of the nonnegative integers strictly less than $224$ equals $24976$. Equivalently, $\\sum_{k=0}^{224-1} k = 224(224-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_224 : ∑ k ∈ range 224, k = 24976 := by sorry

end FiniteTriangular
