-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_87
-- name    : FiniteTriangular.sum_range_87
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:02.079213+00:00
-- url     : https://prove2.me/theorems/1bb44dfa-41fb-41c6-9770-41b26b0ef3f9
-- title:
--   Sum of integers below 87
-- statement:
--   The sum of the nonnegative integers strictly less than $87$ equals $3741$. Equivalently, $\sum_{k=0}^{87-1} k = 87(87-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_87 : ∑ k ∈ range 87, k = 3741 := by sorry

end FiniteTriangular
