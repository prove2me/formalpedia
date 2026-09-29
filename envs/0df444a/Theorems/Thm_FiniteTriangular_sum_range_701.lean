-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_701
-- name    : FiniteTriangular.sum_range_701
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:58.562483+00:00
-- url     : https://prove2.me/theorems/f55ee701-7cbd-4b8a-b55c-5639ba00a0b9
-- title:
--   Sum of integers below 701
-- statement:
--   The sum of the nonnegative integers strictly less than $701$ equals $245350$. Equivalently, $\\sum_{k=0}^{701-1} k = 701(701-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_701 : ∑ k ∈ range 701, k = 245350 := by sorry

end FiniteTriangular
