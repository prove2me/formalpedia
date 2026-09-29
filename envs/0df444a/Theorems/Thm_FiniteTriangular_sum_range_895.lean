-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_895
-- name    : FiniteTriangular.sum_range_895
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:55.392869+00:00
-- url     : https://prove2.me/theorems/364653e4-8ae0-4eef-a000-ec434468e202
-- title:
--   Sum of integers below 895
-- statement:
--   The sum of the nonnegative integers strictly less than $895$ equals $400065$. Equivalently, $\\sum_{k=0}^{895-1} k = 895(895-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_895 : ∑ k ∈ range 895, k = 400065 := by sorry

end FiniteTriangular
