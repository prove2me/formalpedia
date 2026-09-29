-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_557
-- name    : FiniteTriangular.sum_range_557
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:16.587608+00:00
-- url     : https://prove2.me/theorems/bdca54fd-8ad3-429d-8c58-306779839523
-- title:
--   Sum of integers below 557
-- statement:
--   The sum of the nonnegative integers strictly less than $557$ equals $154846$. Equivalently, $\\sum_{k=0}^{557-1} k = 557(557-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_557 : ∑ k ∈ range 557, k = 154846 := by sorry

end FiniteTriangular
