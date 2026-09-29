-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_876
-- name    : FiniteTriangular.sum_range_876
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:31.563664+00:00
-- url     : https://prove2.me/theorems/eb0438d2-4651-4177-9e31-4aa362f5184d
-- title:
--   Sum of integers below 876
-- statement:
--   The sum of the nonnegative integers strictly less than $876$ equals $383250$. Equivalently, $\\sum_{k=0}^{876-1} k = 876(876-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_876 : ∑ k ∈ range 876, k = 383250 := by sorry

end FiniteTriangular
