-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_253
-- name    : FiniteTriangular.sum_range_253
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:04.310291+00:00
-- url     : https://prove2.me/theorems/c01d4d2b-0297-43fe-88d4-315d5207631d
-- title:
--   Sum of integers below 253
-- statement:
--   The sum of the nonnegative integers strictly less than $253$ equals $31878$. Equivalently, $\\sum_{k=0}^{253-1} k = 253(253-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_253 : ∑ k ∈ range 253, k = 31878 := by sorry

end FiniteTriangular
