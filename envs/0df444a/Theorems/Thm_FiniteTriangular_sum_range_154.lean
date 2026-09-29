-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_154
-- name    : FiniteTriangular.sum_range_154
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:21.073497+00:00
-- url     : https://prove2.me/theorems/aa34eef3-5a13-486a-946c-2fea9dd3c5c5
-- title:
--   Sum of integers below 154
-- statement:
--   The sum of the nonnegative integers strictly less than $154$ equals $11781$. Equivalently, $\sum_{k=0}^{154-1} k = 154(154-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_154 : ∑ k ∈ range 154, k = 11781 := by sorry

end FiniteTriangular
