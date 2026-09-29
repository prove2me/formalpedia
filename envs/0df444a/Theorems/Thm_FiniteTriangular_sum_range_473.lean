-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_473
-- name    : FiniteTriangular.sum_range_473
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:25.390781+00:00
-- url     : https://prove2.me/theorems/3847f1e8-42d3-4bb9-aa8c-de50a3be502a
-- title:
--   Sum of integers below 473
-- statement:
--   The sum of the nonnegative integers strictly less than $473$ equals $111628$. Equivalently, $\\sum_{k=0}^{473-1} k = 473(473-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_473 : ∑ k ∈ range 473, k = 111628 := by sorry

end FiniteTriangular
