-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_766
-- name    : FiniteTriangular.sum_range_766
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:37.812333+00:00
-- url     : https://prove2.me/theorems/a3209ff2-9c24-4ed8-9c75-2635cd56c4b2
-- title:
--   Sum of integers below 766
-- statement:
--   The sum of the nonnegative integers strictly less than $766$ equals $292995$. Equivalently, $\\sum_{k=0}^{766-1} k = 766(766-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_766 : ∑ k ∈ range 766, k = 292995 := by sorry

end FiniteTriangular
