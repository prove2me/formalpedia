-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_432
-- name    : FiniteTriangular.sum_range_432
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:42.580279+00:00
-- url     : https://prove2.me/theorems/b6b7e2b0-bb25-4dd1-950a-c56e01aea74b
-- title:
--   Sum of integers below 432
-- statement:
--   The sum of the nonnegative integers strictly less than $432$ equals $93096$. Equivalently, $\\sum_{k=0}^{432-1} k = 432(432-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_432 : ∑ k ∈ range 432, k = 93096 := by sorry

end FiniteTriangular
