-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_306
-- name    : FiniteTriangular.sum_range_306
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:55.086135+00:00
-- url     : https://prove2.me/theorems/0cb8ef4b-3529-45e7-a48c-f81305bda7e4
-- title:
--   Sum of integers below 306
-- statement:
--   The sum of the nonnegative integers strictly less than $306$ equals $46665$. Equivalently, $\\sum_{k=0}^{306-1} k = 306(306-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_306 : ∑ k ∈ range 306, k = 46665 := by sorry

end FiniteTriangular
