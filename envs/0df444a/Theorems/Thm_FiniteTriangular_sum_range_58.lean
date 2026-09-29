-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_58
-- name    : FiniteTriangular.sum_range_58
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:18.37045+00:00
-- url     : https://prove2.me/theorems/b05b5911-6d6c-44eb-bbec-8cb5645b8c22
-- title:
--   Sum of integers below 58
-- statement:
--   The sum of the nonnegative integers strictly less than $58$ equals $1653$. Equivalently, $\sum_{k=0}^{58-1} k = 58(58-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_58 : ∑ k ∈ range 58, k = 1653 := by sorry

end FiniteTriangular
