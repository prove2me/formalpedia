-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_334
-- name    : FiniteTriangular.sum_range_334
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:06.612456+00:00
-- url     : https://prove2.me/theorems/99580d38-b15c-4ec0-bb65-ebb94b6f712b
-- title:
--   Sum of integers below 334
-- statement:
--   The sum of the nonnegative integers strictly less than $334$ equals $55611$. Equivalently, $\\sum_{k=0}^{334-1} k = 334(334-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_334 : ∑ k ∈ range 334, k = 55611 := by sorry

end FiniteTriangular
