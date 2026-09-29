-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_196
-- name    : FiniteTriangular.sum_range_196
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:25.335993+00:00
-- url     : https://prove2.me/theorems/0a15c254-7a46-4cec-ba17-84d2b1628daf
-- title:
--   Sum of integers below 196
-- statement:
--   The sum of the nonnegative integers strictly less than $196$ equals $19110$. Equivalently, $\\sum_{k=0}^{196-1} k = 196(196-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_196 : ∑ k ∈ range 196, k = 19110 := by sorry

end FiniteTriangular
