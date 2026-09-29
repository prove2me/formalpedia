-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_824
-- name    : FiniteTriangular.sum_range_824
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:43.01651+00:00
-- url     : https://prove2.me/theorems/127f7ee0-118a-47bf-94f0-82353c2d7905
-- title:
--   Sum of integers below 824
-- statement:
--   The sum of the nonnegative integers strictly less than $824$ equals $339076$. Equivalently, $\\sum_{k=0}^{824-1} k = 824(824-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_824 : ∑ k ∈ range 824, k = 339076 := by sorry

end FiniteTriangular
