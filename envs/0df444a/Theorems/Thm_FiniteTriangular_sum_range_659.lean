-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_659
-- name    : FiniteTriangular.sum_range_659
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:37.6594+00:00
-- url     : https://prove2.me/theorems/447e53bc-27ad-445d-9d9c-9539d6aea529
-- title:
--   Sum of integers below 659
-- statement:
--   The sum of the nonnegative integers strictly less than $659$ equals $216811$. Equivalently, $\\sum_{k=0}^{659-1} k = 659(659-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_659 : ∑ k ∈ range 659, k = 216811 := by sorry

end FiniteTriangular
