-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_55
-- name    : FiniteTriangular.sum_range_55
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:18:57.916974+00:00
-- url     : https://prove2.me/theorems/069d4992-b92c-4966-93b7-e7fcaf71bf68
-- title:
--   Sum of integers below 55
-- statement:
--   The sum of the nonnegative integers strictly less than $55$ equals $1485$. Equivalently, $\sum_{k=0}^{55-1} k = 55(55-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_55 : ∑ k ∈ range 55, k = 1485 := by sorry

end FiniteTriangular
