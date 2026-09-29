-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_409
-- name    : FiniteTriangular.sum_range_409
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:07.390731+00:00
-- url     : https://prove2.me/theorems/dc560d43-ccf1-449c-896d-bde3decb0d4f
-- title:
--   Sum of integers below 409
-- statement:
--   The sum of the nonnegative integers strictly less than $409$ equals $83436$. Equivalently, $\\sum_{k=0}^{409-1} k = 409(409-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_409 : ∑ k ∈ range 409, k = 83436 := by sorry

end FiniteTriangular
