-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_172
-- name    : FiniteTriangular.sum_range_172
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:23.253988+00:00
-- url     : https://prove2.me/theorems/877fe35d-e8b8-4220-b5dc-75eabd080d9b
-- title:
--   Sum of integers below 172
-- statement:
--   The sum of the nonnegative integers strictly less than $172$ equals $14706$. Equivalently, $\sum_{k=0}^{172-1} k = 172(172-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_172 : ∑ k ∈ range 172, k = 14706 := by sorry

end FiniteTriangular
