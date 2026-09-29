-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_133
-- name    : FiniteTriangular.sum_range_133
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:49.730787+00:00
-- url     : https://prove2.me/theorems/8bb2964d-fcff-4353-af56-fa3aeafb9480
-- title:
--   Sum of integers below 133
-- statement:
--   The sum of the nonnegative integers strictly less than $133$ equals $8778$. Equivalently, $\sum_{k=0}^{133-1} k = 133(133-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_133 : ∑ k ∈ range 133, k = 8778 := by sorry

end FiniteTriangular
