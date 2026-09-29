-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_426
-- name    : FiniteTriangular.sum_range_426
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:39.571083+00:00
-- url     : https://prove2.me/theorems/de5ca8d0-d098-46f0-a044-3e02ec196787
-- title:
--   Sum of integers below 426
-- statement:
--   The sum of the nonnegative integers strictly less than $426$ equals $90525$. Equivalently, $\\sum_{k=0}^{426-1} k = 426(426-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_426 : ∑ k ∈ range 426, k = 90525 := by sorry

end FiniteTriangular
