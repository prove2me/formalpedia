-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_936
-- name    : FiniteTriangular.sum_range_936
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:14.106498+00:00
-- url     : https://prove2.me/theorems/b9469f9a-e7a0-4a3c-aa3f-f4d9d40bf19c
-- title:
--   Sum of integers below 936
-- statement:
--   The sum of the nonnegative integers strictly less than $936$ equals $437580$. Equivalently, $\\sum_{k=0}^{936-1} k = 936(936-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_936 : ∑ k ∈ range 936, k = 437580 := by sorry

end FiniteTriangular
