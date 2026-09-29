-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_48
-- name    : FiniteTriangular.sum_range_48
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:12.075986+00:00
-- url     : https://prove2.me/theorems/6718c42e-ac8c-4e80-98d7-c37132b2703c
-- title:
--   Sum of integers below 48
-- statement:
--   The sum of the nonnegative integers strictly less than $48$ equals $1128$. Equivalently, $\sum_{k=0}^{48-1} k = 48(48-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_48 : ∑ k ∈ range 48, k = 1128 := by sorry

end FiniteTriangular
