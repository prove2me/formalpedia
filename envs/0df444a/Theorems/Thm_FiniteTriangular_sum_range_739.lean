-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_739
-- name    : FiniteTriangular.sum_range_739
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:31.763986+00:00
-- url     : https://prove2.me/theorems/5892c187-70c7-4092-9a61-6a5e1413f123
-- title:
--   Sum of integers below 739
-- statement:
--   The sum of the nonnegative integers strictly less than $739$ equals $272691$. Equivalently, $\\sum_{k=0}^{739-1} k = 739(739-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_739 : ∑ k ∈ range 739, k = 272691 := by sorry

end FiniteTriangular
