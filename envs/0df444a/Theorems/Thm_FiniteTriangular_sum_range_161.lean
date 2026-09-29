-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_161
-- name    : FiniteTriangular.sum_range_161
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:51.794745+00:00
-- url     : https://prove2.me/theorems/3cff0f86-da71-4789-a25b-9fc2febec78c
-- title:
--   Sum of integers below 161
-- statement:
--   The sum of the nonnegative integers strictly less than $161$ equals $12880$. Equivalently, $\sum_{k=0}^{161-1} k = 161(161-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_161 : ∑ k ∈ range 161, k = 12880 := by sorry

end FiniteTriangular
