-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_288
-- name    : FiniteTriangular.sum_range_288
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:30.49425+00:00
-- url     : https://prove2.me/theorems/a7d7177f-230b-40d2-adc2-9324cf7a1898
-- title:
--   Sum of integers below 288
-- statement:
--   The sum of the nonnegative integers strictly less than $288$ equals $41328$. Equivalently, $\\sum_{k=0}^{288-1} k = 288(288-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_288 : ∑ k ∈ range 288, k = 41328 := by sorry

end FiniteTriangular
