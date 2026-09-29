-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_159
-- name    : FiniteTriangular.sum_range_159
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:18.973483+00:00
-- url     : https://prove2.me/theorems/810d3822-09f9-4f11-a521-e6775d853fd7
-- title:
--   Sum of integers below 159
-- statement:
--   The sum of the nonnegative integers strictly less than $159$ equals $12561$. Equivalently, $\sum_{k=0}^{159-1} k = 159(159-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_159 : ∑ k ∈ range 159, k = 12561 := by sorry

end FiniteTriangular
