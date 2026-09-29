-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_312
-- name    : FiniteTriangular.sum_range_312
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:54.012231+00:00
-- url     : https://prove2.me/theorems/7de6a5d2-006d-4fef-94ae-3a4e9878f3d8
-- title:
--   Sum of integers below 312
-- statement:
--   The sum of the nonnegative integers strictly less than $312$ equals $48516$. Equivalently, $\\sum_{k=0}^{312-1} k = 312(312-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_312 : ∑ k ∈ range 312, k = 48516 := by sorry

end FiniteTriangular
