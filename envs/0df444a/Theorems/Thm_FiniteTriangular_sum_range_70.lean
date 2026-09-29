-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_70
-- name    : FiniteTriangular.sum_range_70
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:57.666693+00:00
-- url     : https://prove2.me/theorems/1fcf7275-4a1c-4537-979e-34c7f024ed5d
-- title:
--   Sum of integers below 70
-- statement:
--   The sum of the nonnegative integers strictly less than $70$ equals $2415$. Equivalently, $\sum_{k=0}^{70-1} k = 70(70-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_70 : ∑ k ∈ range 70, k = 2415 := by sorry

end FiniteTriangular
