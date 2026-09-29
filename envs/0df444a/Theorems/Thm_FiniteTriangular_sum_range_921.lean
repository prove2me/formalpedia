-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_921
-- name    : FiniteTriangular.sum_range_921
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:34.319546+00:00
-- url     : https://prove2.me/theorems/5bd9e630-d25c-44aa-a8e8-deb214f7343b
-- title:
--   Sum of integers below 921
-- statement:
--   The sum of the nonnegative integers strictly less than $921$ equals $423660$. Equivalently, $\\sum_{k=0}^{921-1} k = 921(921-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_921 : ∑ k ∈ range 921, k = 423660 := by sorry

end FiniteTriangular
