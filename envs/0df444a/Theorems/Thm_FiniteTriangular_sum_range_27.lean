-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_27
-- name    : FiniteTriangular.sum_range_27
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:07.494153+00:00
-- url     : https://prove2.me/theorems/7b8f9057-8c83-41b7-b2c3-6e8b48acde0a
-- title:
--   Sum of integers below 27
-- statement:
--   The sum of the nonnegative integers strictly less than $27$ equals $351$. Equivalently, $\sum_{k=0}^{27-1} k = 27(27-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_27 : ∑ k ∈ range 27, k = 351 := by sorry

end FiniteTriangular
