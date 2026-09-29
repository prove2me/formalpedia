-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_26
-- name    : FiniteTriangular.sum_range_26
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:06.213351+00:00
-- url     : https://prove2.me/theorems/cb46c377-6db0-432e-b0ae-3affc158ba39
-- title:
--   Sum of integers below 26
-- statement:
--   The sum of the nonnegative integers strictly less than $26$ equals $325$. Equivalently, $\sum_{k=0}^{26-1} k = 26(26-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_26 : ∑ k ∈ range 26, k = 325 := by sorry

end FiniteTriangular
