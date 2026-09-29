-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_165
-- name    : FiniteTriangular.sum_range_165
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:52.972313+00:00
-- url     : https://prove2.me/theorems/6f635983-9e8b-4dd3-95dd-3dd9585661e8
-- title:
--   Sum of integers below 165
-- statement:
--   The sum of the nonnegative integers strictly less than $165$ equals $13530$. Equivalently, $\sum_{k=0}^{165-1} k = 165(165-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_165 : ∑ k ∈ range 165, k = 13530 := by sorry

end FiniteTriangular
