-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_354
-- name    : FiniteTriangular.sum_range_354
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:15.759903+00:00
-- url     : https://prove2.me/theorems/d8894ac6-72a9-49a8-b0a2-19c5943fde9c
-- title:
--   Sum of integers below 354
-- statement:
--   The sum of the nonnegative integers strictly less than $354$ equals $62481$. Equivalently, $\\sum_{k=0}^{354-1} k = 354(354-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_354 : ∑ k ∈ range 354, k = 62481 := by sorry

end FiniteTriangular
