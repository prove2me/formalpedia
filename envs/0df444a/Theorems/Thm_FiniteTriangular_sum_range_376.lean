-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_376
-- name    : FiniteTriangular.sum_range_376
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:04.456418+00:00
-- url     : https://prove2.me/theorems/b76f9584-edba-4a44-987f-1ced79e72b36
-- title:
--   Sum of integers below 376
-- statement:
--   The sum of the nonnegative integers strictly less than $376$ equals $70500$. Equivalently, $\\sum_{k=0}^{376-1} k = 376(376-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_376 : ∑ k ∈ range 376, k = 70500 := by sorry

end FiniteTriangular
