-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_710
-- name    : FiniteTriangular.sum_range_710
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:47.490824+00:00
-- url     : https://prove2.me/theorems/eaea029b-7c7d-4c30-9b88-3c107c1fc669
-- title:
--   Sum of integers below 710
-- statement:
--   The sum of the nonnegative integers strictly less than $710$ equals $251695$. Equivalently, $\\sum_{k=0}^{710-1} k = 710(710-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_710 : ∑ k ∈ range 710, k = 251695 := by sorry

end FiniteTriangular
