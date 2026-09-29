-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_179
-- name    : FiniteTriangular.sum_range_179
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:05.942496+00:00
-- url     : https://prove2.me/theorems/cedb19b4-39ed-4a4c-9dff-43e328caa1a9
-- title:
--   Sum of integers below 179
-- statement:
--   The sum of the nonnegative integers strictly less than $179$ equals $15931$. Equivalently, $\sum_{k=0}^{179-1} k = 179(179-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_179 : ∑ k ∈ range 179, k = 15931 := by sorry

end FiniteTriangular
