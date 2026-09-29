-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_874
-- name    : FiniteTriangular.sum_range_874
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:28.281238+00:00
-- url     : https://prove2.me/theorems/6c29ef6b-3caf-4f28-ab64-c5301bcdc6bd
-- title:
--   Sum of integers below 874
-- statement:
--   The sum of the nonnegative integers strictly less than $874$ equals $381501$. Equivalently, $\\sum_{k=0}^{874-1} k = 874(874-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_874 : ∑ k ∈ range 874, k = 381501 := by sorry

end FiniteTriangular
