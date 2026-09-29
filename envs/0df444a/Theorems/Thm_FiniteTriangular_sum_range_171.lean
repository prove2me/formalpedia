-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_171
-- name    : FiniteTriangular.sum_range_171
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:20.473659+00:00
-- url     : https://prove2.me/theorems/e23c1a6e-0f5c-400f-bc88-cff4555e56f0
-- title:
--   Sum of integers below 171
-- statement:
--   The sum of the nonnegative integers strictly less than $171$ equals $14535$. Equivalently, $\sum_{k=0}^{171-1} k = 171(171-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_171 : ∑ k ∈ range 171, k = 14535 := by sorry

end FiniteTriangular
