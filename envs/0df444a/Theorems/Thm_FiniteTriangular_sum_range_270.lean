-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_270
-- name    : FiniteTriangular.sum_range_270
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:46.907013+00:00
-- url     : https://prove2.me/theorems/9858595c-7313-41dd-aedb-cd567ef538d4
-- title:
--   Sum of integers below 270
-- statement:
--   The sum of the nonnegative integers strictly less than $270$ equals $36315$. Equivalently, $\\sum_{k=0}^{270-1} k = 270(270-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_270 : ∑ k ∈ range 270, k = 36315 := by sorry

end FiniteTriangular
