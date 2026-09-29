-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_459
-- name    : FiniteTriangular.sum_range_459
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:44.51261+00:00
-- url     : https://prove2.me/theorems/f9279129-29ec-47e8-9905-566c0116c050
-- title:
--   Sum of integers below 459
-- statement:
--   The sum of the nonnegative integers strictly less than $459$ equals $105111$. Equivalently, $\\sum_{k=0}^{459-1} k = 459(459-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_459 : ∑ k ∈ range 459, k = 105111 := by sorry

end FiniteTriangular
