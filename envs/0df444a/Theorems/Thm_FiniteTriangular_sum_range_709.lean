-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_709
-- name    : FiniteTriangular.sum_range_709
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:48.940113+00:00
-- url     : https://prove2.me/theorems/698a39ca-bb86-4f83-b58c-48caf0d9e586
-- title:
--   Sum of integers below 709
-- statement:
--   The sum of the nonnegative integers strictly less than $709$ equals $250986$. Equivalently, $\\sum_{k=0}^{709-1} k = 709(709-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_709 : ∑ k ∈ range 709, k = 250986 := by sorry

end FiniteTriangular
