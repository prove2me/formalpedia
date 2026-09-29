-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_91
-- name    : FiniteTriangular.sum_range_91
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:40.186984+00:00
-- url     : https://prove2.me/theorems/cd04533f-c1b6-4889-9fbb-73074a7e7c29
-- title:
--   Sum of integers below 91
-- statement:
--   The sum of the nonnegative integers strictly less than $91$ equals $4095$. Equivalently, $\sum_{k=0}^{91-1} k = 91(91-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_91 : ∑ k ∈ range 91, k = 4095 := by sorry

end FiniteTriangular
