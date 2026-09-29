-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_601
-- name    : FiniteTriangular.sum_range_601
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:43.965266+00:00
-- url     : https://prove2.me/theorems/5ad57972-c4a8-4207-86ef-491c832d08f3
-- title:
--   Sum of integers below 601
-- statement:
--   The sum of the nonnegative integers strictly less than $601$ equals $180300$. Equivalently, $\\sum_{k=0}^{601-1} k = 601(601-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_601 : ∑ k ∈ range 601, k = 180300 := by sorry

end FiniteTriangular
