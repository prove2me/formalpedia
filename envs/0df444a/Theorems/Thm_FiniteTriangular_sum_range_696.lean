-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_696
-- name    : FiniteTriangular.sum_range_696
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:25.983853+00:00
-- url     : https://prove2.me/theorems/adebcef9-510c-4e7d-9454-e9b23a59224f
-- title:
--   Sum of integers below 696
-- statement:
--   The sum of the nonnegative integers strictly less than $696$ equals $241860$. Equivalently, $\\sum_{k=0}^{696-1} k = 696(696-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_696 : ∑ k ∈ range 696, k = 241860 := by sorry

end FiniteTriangular
