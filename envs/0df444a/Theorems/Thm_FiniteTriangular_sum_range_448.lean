-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_448
-- name    : FiniteTriangular.sum_range_448
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:06.433784+00:00
-- url     : https://prove2.me/theorems/29115b86-911a-40bc-8a1e-c4a1b47a2126
-- title:
--   Sum of integers below 448
-- statement:
--   The sum of the nonnegative integers strictly less than $448$ equals $100128$. Equivalently, $\\sum_{k=0}^{448-1} k = 448(448-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_448 : ∑ k ∈ range 448, k = 100128 := by sorry

end FiniteTriangular
