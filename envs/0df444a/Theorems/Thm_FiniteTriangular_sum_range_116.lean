-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_116
-- name    : FiniteTriangular.sum_range_116
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:07.056926+00:00
-- url     : https://prove2.me/theorems/c39372c3-8a71-4746-a175-36b0fd7e7d1a
-- title:
--   Sum of integers below 116
-- statement:
--   The sum of the nonnegative integers strictly less than $116$ equals $6670$. Equivalently, $\sum_{k=0}^{116-1} k = 116(116-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_116 : ∑ k ∈ range 116, k = 6670 := by sorry

end FiniteTriangular
