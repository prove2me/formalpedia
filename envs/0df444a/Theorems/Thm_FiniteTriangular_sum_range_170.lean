-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_170
-- name    : FiniteTriangular.sum_range_170
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:20.1237+00:00
-- url     : https://prove2.me/theorems/3bbd682d-fb7b-4c41-acf7-90ab361ab127
-- title:
--   Sum of integers below 170
-- statement:
--   The sum of the nonnegative integers strictly less than $170$ equals $14365$. Equivalently, $\sum_{k=0}^{170-1} k = 170(170-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_170 : ∑ k ∈ range 170, k = 14365 := by sorry

end FiniteTriangular
