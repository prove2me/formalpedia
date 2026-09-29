-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_23
-- name    : FiniteTriangular.sum_range_23
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:08:12.116508+00:00
-- url     : https://prove2.me/theorems/5547d41e-15e9-47e8-90ec-9615f0897a32
-- title:
--   Sum of integers below 23
-- statement:
--   The sum of the nonnegative integers strictly less than $23$ equals $253$. Equivalently, $\sum_{k=0}^{23-1} k = 23(23-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_23 : ∑ k ∈ range 23, k = 253 := by sorry

end FiniteTriangular
