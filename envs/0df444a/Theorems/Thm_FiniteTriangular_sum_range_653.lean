-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_653
-- name    : FiniteTriangular.sum_range_653
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:49.797461+00:00
-- url     : https://prove2.me/theorems/dcbcf097-e64a-4885-826f-621ba5e9e18e
-- title:
--   Sum of integers below 653
-- statement:
--   The sum of the nonnegative integers strictly less than $653$ equals $212878$. Equivalently, $\\sum_{k=0}^{653-1} k = 653(653-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_653 : ∑ k ∈ range 653, k = 212878 := by sorry

end FiniteTriangular
