-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_634
-- name    : FiniteTriangular.sum_range_634
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:40.176047+00:00
-- url     : https://prove2.me/theorems/7f120dd0-e18d-43cb-8839-9aebfdeea73a
-- title:
--   Sum of integers below 634
-- statement:
--   The sum of the nonnegative integers strictly less than $634$ equals $200661$. Equivalently, $\\sum_{k=0}^{634-1} k = 634(634-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_634 : ∑ k ∈ range 634, k = 200661 := by sorry

end FiniteTriangular
