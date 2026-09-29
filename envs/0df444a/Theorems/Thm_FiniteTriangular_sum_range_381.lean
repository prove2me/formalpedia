-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_381
-- name    : FiniteTriangular.sum_range_381
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:14.189456+00:00
-- url     : https://prove2.me/theorems/1a68db84-a0ca-426f-9266-95223667ca2f
-- title:
--   Sum of integers below 381
-- statement:
--   The sum of the nonnegative integers strictly less than $381$ equals $72390$. Equivalently, $\\sum_{k=0}^{381-1} k = 381(381-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_381 : ∑ k ∈ range 381, k = 72390 := by sorry

end FiniteTriangular
