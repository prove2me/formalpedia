-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_630
-- name    : FiniteTriangular.sum_range_630
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:52.565717+00:00
-- url     : https://prove2.me/theorems/1d606dec-4389-4241-b9fa-5885a5b825b3
-- title:
--   Sum of integers below 630
-- statement:
--   The sum of the nonnegative integers strictly less than $630$ equals $198135$. Equivalently, $\\sum_{k=0}^{630-1} k = 630(630-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_630 : ∑ k ∈ range 630, k = 198135 := by sorry

end FiniteTriangular
