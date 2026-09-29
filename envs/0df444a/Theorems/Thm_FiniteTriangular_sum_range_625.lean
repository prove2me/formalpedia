-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_625
-- name    : FiniteTriangular.sum_range_625
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:51.397286+00:00
-- url     : https://prove2.me/theorems/b62b2703-6554-445b-8aeb-f5900b2d0f2b
-- title:
--   Sum of integers below 625
-- statement:
--   The sum of the nonnegative integers strictly less than $625$ equals $195000$. Equivalently, $\\sum_{k=0}^{625-1} k = 625(625-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_625 : ∑ k ∈ range 625, k = 195000 := by sorry

end FiniteTriangular
