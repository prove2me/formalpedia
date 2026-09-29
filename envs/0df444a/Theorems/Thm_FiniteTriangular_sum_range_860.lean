-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_860
-- name    : FiniteTriangular.sum_range_860
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:58.732446+00:00
-- url     : https://prove2.me/theorems/c92aa16f-21d1-4a07-82e3-086c2b5b8bd0
-- title:
--   Sum of integers below 860
-- statement:
--   The sum of the nonnegative integers strictly less than $860$ equals $369370$. Equivalently, $\\sum_{k=0}^{860-1} k = 860(860-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_860 : ∑ k ∈ range 860, k = 369370 := by sorry

end FiniteTriangular
