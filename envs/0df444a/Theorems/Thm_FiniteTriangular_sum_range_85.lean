-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_85
-- name    : FiniteTriangular.sum_range_85
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:01.533296+00:00
-- url     : https://prove2.me/theorems/2c5b8861-3e3e-4f4f-8eff-e55ae1b46c94
-- title:
--   Sum of integers below 85
-- statement:
--   The sum of the nonnegative integers strictly less than $85$ equals $3570$. Equivalently, $\sum_{k=0}^{85-1} k = 85(85-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_85 : ∑ k ∈ range 85, k = 3570 := by sorry

end FiniteTriangular
