-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_320
-- name    : FiniteTriangular.sum_range_320
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:27.11437+00:00
-- url     : https://prove2.me/theorems/6207e07a-13a0-46a4-b1c3-a402940ac2a4
-- title:
--   Sum of integers below 320
-- statement:
--   The sum of the nonnegative integers strictly less than $320$ equals $51040$. Equivalently, $\\sum_{k=0}^{320-1} k = 320(320-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_320 : ∑ k ∈ range 320, k = 51040 := by sorry

end FiniteTriangular
