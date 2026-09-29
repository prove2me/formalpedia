-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_383
-- name    : FiniteTriangular.sum_range_383
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:13.903447+00:00
-- url     : https://prove2.me/theorems/6ad9e974-b7ec-4335-82c2-7a225268f3d3
-- title:
--   Sum of integers below 383
-- statement:
--   The sum of the nonnegative integers strictly less than $383$ equals $73153$. Equivalently, $\\sum_{k=0}^{383-1} k = 383(383-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_383 : ∑ k ∈ range 383, k = 73153 := by sorry

end FiniteTriangular
