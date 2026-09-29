-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_287
-- name    : FiniteTriangular.sum_range_287
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:32.369172+00:00
-- url     : https://prove2.me/theorems/a6f49f3b-5312-4c6f-9671-0ee01cb8a1cc
-- title:
--   Sum of integers below 287
-- statement:
--   The sum of the nonnegative integers strictly less than $287$ equals $41041$. Equivalently, $\\sum_{k=0}^{287-1} k = 287(287-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_287 : ∑ k ∈ range 287, k = 41041 := by sorry

end FiniteTriangular
