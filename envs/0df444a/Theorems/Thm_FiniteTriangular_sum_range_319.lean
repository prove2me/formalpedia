-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_319
-- name    : FiniteTriangular.sum_range_319
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:28.613409+00:00
-- url     : https://prove2.me/theorems/ea004a9d-6d55-4d1f-8256-969dff463520
-- title:
--   Sum of integers below 319
-- statement:
--   The sum of the nonnegative integers strictly less than $319$ equals $50721$. Equivalently, $\\sum_{k=0}^{319-1} k = 319(319-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_319 : ∑ k ∈ range 319, k = 50721 := by sorry

end FiniteTriangular
