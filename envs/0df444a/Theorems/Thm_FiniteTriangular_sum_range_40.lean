-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_40
-- name    : FiniteTriangular.sum_range_40
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:55.995992+00:00
-- url     : https://prove2.me/theorems/10c4a275-9bac-495a-b3e3-03538278b729
-- title:
--   Sum of integers below 40
-- statement:
--   The sum of the nonnegative integers strictly less than $40$ equals $780$. Equivalently, $\sum_{k=0}^{40-1} k = 40(40-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_40 : ∑ k ∈ range 40, k = 780 := by sorry

end FiniteTriangular
