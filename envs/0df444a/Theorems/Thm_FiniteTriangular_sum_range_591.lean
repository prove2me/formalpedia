-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_591
-- name    : FiniteTriangular.sum_range_591
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:23.290482+00:00
-- url     : https://prove2.me/theorems/bad42221-11e1-4472-a83e-96fa5c172087
-- title:
--   Sum of integers below 591
-- statement:
--   The sum of the nonnegative integers strictly less than $591$ equals $174345$. Equivalently, $\\sum_{k=0}^{591-1} k = 591(591-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_591 : ∑ k ∈ range 591, k = 174345 := by sorry

end FiniteTriangular
