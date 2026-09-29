-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_209
-- name    : FiniteTriangular.sum_range_209
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:36.494505+00:00
-- url     : https://prove2.me/theorems/c2dd0d59-a2e5-4832-9682-62a00903d86b
-- title:
--   Sum of integers below 209
-- statement:
--   The sum of the nonnegative integers strictly less than $209$ equals $21736$. Equivalently, $\\sum_{k=0}^{209-1} k = 209(209-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_209 : ∑ k ∈ range 209, k = 21736 := by sorry

end FiniteTriangular
