-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_453
-- name    : FiniteTriangular.sum_range_453
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:52.261869+00:00
-- url     : https://prove2.me/theorems/d113d4eb-57ac-4eb2-9248-60b6cacba8a3
-- title:
--   Sum of integers below 453
-- statement:
--   The sum of the nonnegative integers strictly less than $453$ equals $102378$. Equivalently, $\\sum_{k=0}^{453-1} k = 453(453-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_453 : ∑ k ∈ range 453, k = 102378 := by sorry

end FiniteTriangular
