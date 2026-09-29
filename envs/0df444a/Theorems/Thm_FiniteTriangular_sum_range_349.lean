-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_349
-- name    : FiniteTriangular.sum_range_349
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:38.425841+00:00
-- url     : https://prove2.me/theorems/43a93053-dfd9-4bc5-93e1-ba1b8198602f
-- title:
--   Sum of integers below 349
-- statement:
--   The sum of the nonnegative integers strictly less than $349$ equals $60726$. Equivalently, $\\sum_{k=0}^{349-1} k = 349(349-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_349 : ∑ k ∈ range 349, k = 60726 := by sorry

end FiniteTriangular
