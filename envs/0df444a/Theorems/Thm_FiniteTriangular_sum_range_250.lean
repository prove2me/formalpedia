-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_250
-- name    : FiniteTriangular.sum_range_250
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:03.709857+00:00
-- url     : https://prove2.me/theorems/ad734171-013a-42d4-8b06-0e6eaf3f973c
-- title:
--   Sum of integers below 250
-- statement:
--   The sum of the nonnegative integers strictly less than $250$ equals $31125$. Equivalently, $\\sum_{k=0}^{250-1} k = 250(250-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_250 : ∑ k ∈ range 250, k = 31125 := by sorry

end FiniteTriangular
