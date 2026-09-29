-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_683
-- name    : FiniteTriangular.sum_range_683
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:47.134476+00:00
-- url     : https://prove2.me/theorems/f5b9cfbb-42b4-413c-87d8-1c9e9e3c1ef9
-- title:
--   Sum of integers below 683
-- statement:
--   The sum of the nonnegative integers strictly less than $683$ equals $232903$. Equivalently, $\\sum_{k=0}^{683-1} k = 683(683-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_683 : ∑ k ∈ range 683, k = 232903 := by sorry

end FiniteTriangular
