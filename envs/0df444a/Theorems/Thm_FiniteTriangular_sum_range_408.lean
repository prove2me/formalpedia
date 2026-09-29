-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_408
-- name    : FiniteTriangular.sum_range_408
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:24.268985+00:00
-- url     : https://prove2.me/theorems/2c200427-9f13-477a-aba6-aa797d2d4f5a
-- title:
--   Sum of integers below 408
-- statement:
--   The sum of the nonnegative integers strictly less than $408$ equals $83028$. Equivalently, $\\sum_{k=0}^{408-1} k = 408(408-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_408 : ∑ k ∈ range 408, k = 83028 := by sorry

end FiniteTriangular
