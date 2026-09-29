-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_566
-- name    : FiniteTriangular.sum_range_566
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:07.160714+00:00
-- url     : https://prove2.me/theorems/d44a0078-d2d3-4ae1-87b4-ff539188df2e
-- title:
--   Sum of integers below 566
-- statement:
--   The sum of the nonnegative integers strictly less than $566$ equals $159895$. Equivalently, $\\sum_{k=0}^{566-1} k = 566(566-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_566 : ∑ k ∈ range 566, k = 159895 := by sorry

end FiniteTriangular
