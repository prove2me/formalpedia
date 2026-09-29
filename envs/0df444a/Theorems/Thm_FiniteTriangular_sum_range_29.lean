-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_29
-- name    : FiniteTriangular.sum_range_29
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:07.595328+00:00
-- url     : https://prove2.me/theorems/c50a928c-ee9a-4320-8a98-c450ba593f01
-- title:
--   Sum of integers below 29
-- statement:
--   The sum of the nonnegative integers strictly less than $29$ equals $406$. Equivalently, $\sum_{k=0}^{29-1} k = 29(29-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_29 : ∑ k ∈ range 29, k = 406 := by sorry

end FiniteTriangular
