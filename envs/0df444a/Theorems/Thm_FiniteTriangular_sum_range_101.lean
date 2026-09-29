-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_101
-- name    : FiniteTriangular.sum_range_101
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:23.946387+00:00
-- url     : https://prove2.me/theorems/18674e43-d94b-4fde-8b1b-038af9535b5e
-- title:
--   Sum of integers below 101
-- statement:
--   The sum of the nonnegative integers strictly less than $101$ equals $5050$. Equivalently, $\sum_{k=0}^{101-1} k = 101(101-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_101 : ∑ k ∈ range 101, k = 5050 := by sorry

end FiniteTriangular
