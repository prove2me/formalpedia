-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_387
-- name    : FiniteTriangular.sum_range_387
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:47:01.678338+00:00
-- url     : https://prove2.me/theorems/8fdf6b1c-c155-4f5e-ac66-27ca6204c503
-- title:
--   Sum of integers below 387
-- statement:
--   The sum of the nonnegative integers strictly less than $387$ equals $74691$. Equivalently, $\\sum_{k=0}^{387-1} k = 387(387-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_387 : ∑ k ∈ range 387, k = 74691 := by sorry

end FiniteTriangular
