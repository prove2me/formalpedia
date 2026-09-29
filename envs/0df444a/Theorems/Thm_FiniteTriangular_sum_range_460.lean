-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_460
-- name    : FiniteTriangular.sum_range_460
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:47.050251+00:00
-- url     : https://prove2.me/theorems/6a2c84fe-5f43-42ec-bb8b-f164fb13877e
-- title:
--   Sum of integers below 460
-- statement:
--   The sum of the nonnegative integers strictly less than $460$ equals $105570$. Equivalently, $\\sum_{k=0}^{460-1} k = 460(460-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_460 : ∑ k ∈ range 460, k = 105570 := by sorry

end FiniteTriangular
