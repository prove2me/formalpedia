-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_119
-- name    : FiniteTriangular.sum_range_119
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:08.084056+00:00
-- url     : https://prove2.me/theorems/39757e95-0176-4b7b-876d-32c97a0611b0
-- title:
--   Sum of integers below 119
-- statement:
--   The sum of the nonnegative integers strictly less than $119$ equals $7021$. Equivalently, $\sum_{k=0}^{119-1} k = 119(119-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_119 : ∑ k ∈ range 119, k = 7021 := by sorry

end FiniteTriangular
