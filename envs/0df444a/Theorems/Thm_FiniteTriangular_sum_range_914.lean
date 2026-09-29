-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_914
-- name    : FiniteTriangular.sum_range_914
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:49.5857+00:00
-- url     : https://prove2.me/theorems/d4e849e3-0d2a-4fd1-acde-5e93d3053625
-- title:
--   Sum of integers below 914
-- statement:
--   The sum of the nonnegative integers strictly less than $914$ equals $417241$. Equivalently, $\\sum_{k=0}^{914-1} k = 914(914-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_914 : ∑ k ∈ range 914, k = 417241 := by sorry

end FiniteTriangular
