-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_203
-- name    : FiniteTriangular.sum_range_203
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:22.210427+00:00
-- url     : https://prove2.me/theorems/e1f3addd-c917-4fd4-a198-8e05f87cbb14
-- title:
--   Sum of integers below 203
-- statement:
--   The sum of the nonnegative integers strictly less than $203$ equals $20503$. Equivalently, $\\sum_{k=0}^{203-1} k = 203(203-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_203 : ∑ k ∈ range 203, k = 20503 := by sorry

end FiniteTriangular
