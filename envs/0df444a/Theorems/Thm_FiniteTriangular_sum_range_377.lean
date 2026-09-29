-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_377
-- name    : FiniteTriangular.sum_range_377
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:12.450906+00:00
-- url     : https://prove2.me/theorems/2f76f43a-e25a-4536-a648-d718f2b0f996
-- title:
--   Sum of integers below 377
-- statement:
--   The sum of the nonnegative integers strictly less than $377$ equals $70876$. Equivalently, $\\sum_{k=0}^{377-1} k = 377(377-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_377 : ∑ k ∈ range 377, k = 70876 := by sorry

end FiniteTriangular
