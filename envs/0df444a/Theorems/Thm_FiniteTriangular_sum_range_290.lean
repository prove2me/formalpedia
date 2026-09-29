-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_290
-- name    : FiniteTriangular.sum_range_290
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:05.961372+00:00
-- url     : https://prove2.me/theorems/2ed92398-bb47-4e5f-bfc2-4c6cbb5a6bec
-- title:
--   Sum of integers below 290
-- statement:
--   The sum of the nonnegative integers strictly less than $290$ equals $41905$. Equivalently, $\\sum_{k=0}^{290-1} k = 290(290-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_290 : ∑ k ∈ range 290, k = 41905 := by sorry

end FiniteTriangular
