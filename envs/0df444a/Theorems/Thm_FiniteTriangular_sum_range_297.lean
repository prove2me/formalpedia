-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_297
-- name    : FiniteTriangular.sum_range_297
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:54.392945+00:00
-- url     : https://prove2.me/theorems/6780a365-db60-4289-8a3b-d3114a0fdc3a
-- title:
--   Sum of integers below 297
-- statement:
--   The sum of the nonnegative integers strictly less than $297$ equals $43956$. Equivalently, $\\sum_{k=0}^{297-1} k = 297(297-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_297 : ∑ k ∈ range 297, k = 43956 := by sorry

end FiniteTriangular
