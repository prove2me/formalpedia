-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_176
-- name    : FiniteTriangular.sum_range_176
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:21.497339+00:00
-- url     : https://prove2.me/theorems/d752845a-818d-4144-98eb-b7327f8f353c
-- title:
--   Sum of integers below 176
-- statement:
--   The sum of the nonnegative integers strictly less than $176$ equals $15400$. Equivalently, $\sum_{k=0}^{176-1} k = 176(176-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_176 : ∑ k ∈ range 176, k = 15400 := by sorry

end FiniteTriangular
