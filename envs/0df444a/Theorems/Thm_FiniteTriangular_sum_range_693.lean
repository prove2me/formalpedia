-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_693
-- name    : FiniteTriangular.sum_range_693
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:26.04076+00:00
-- url     : https://prove2.me/theorems/717d5b31-3c5c-4990-b481-4cc495529072
-- title:
--   Sum of integers below 693
-- statement:
--   The sum of the nonnegative integers strictly less than $693$ equals $239778$. Equivalently, $\\sum_{k=0}^{693-1} k = 693(693-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_693 : ∑ k ∈ range 693, k = 239778 := by sorry

end FiniteTriangular
