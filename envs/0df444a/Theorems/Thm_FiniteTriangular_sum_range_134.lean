-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_134
-- name    : FiniteTriangular.sum_range_134
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:54.129618+00:00
-- url     : https://prove2.me/theorems/617c9ce2-1f9e-4bed-8b2a-db4a1b761633
-- title:
--   Sum of integers below 134
-- statement:
--   The sum of the nonnegative integers strictly less than $134$ equals $8911$. Equivalently, $\sum_{k=0}^{134-1} k = 134(134-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_134 : ∑ k ∈ range 134, k = 8911 := by sorry

end FiniteTriangular
