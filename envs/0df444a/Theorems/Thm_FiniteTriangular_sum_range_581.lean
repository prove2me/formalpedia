-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_581
-- name    : FiniteTriangular.sum_range_581
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:36.548489+00:00
-- url     : https://prove2.me/theorems/ecf30285-b1cf-411d-8d5f-311f87c94b2f
-- title:
--   Sum of integers below 581
-- statement:
--   The sum of the nonnegative integers strictly less than $581$ equals $168490$. Equivalently, $\\sum_{k=0}^{581-1} k = 581(581-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_581 : ∑ k ∈ range 581, k = 168490 := by sorry

end FiniteTriangular
