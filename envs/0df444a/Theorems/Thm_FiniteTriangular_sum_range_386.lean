-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_386
-- name    : FiniteTriangular.sum_range_386
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:46:58.810178+00:00
-- url     : https://prove2.me/theorems/43b2d028-58a7-4c74-b295-a1516da20842
-- title:
--   Sum of integers below 386
-- statement:
--   The sum of the nonnegative integers strictly less than $386$ equals $74305$. Equivalently, $\\sum_{k=0}^{386-1} k = 386(386-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_386 : ∑ k ∈ range 386, k = 74305 := by sorry

end FiniteTriangular
