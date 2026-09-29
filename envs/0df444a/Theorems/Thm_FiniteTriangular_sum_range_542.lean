-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_542
-- name    : FiniteTriangular.sum_range_542
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:56.36361+00:00
-- url     : https://prove2.me/theorems/49a291b7-e800-4158-99cf-b627f2e2dca0
-- title:
--   Sum of integers below 542
-- statement:
--   The sum of the nonnegative integers strictly less than $542$ equals $146611$. Equivalently, $\\sum_{k=0}^{542-1} k = 542(542-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_542 : ∑ k ∈ range 542, k = 146611 := by sorry

end FiniteTriangular
