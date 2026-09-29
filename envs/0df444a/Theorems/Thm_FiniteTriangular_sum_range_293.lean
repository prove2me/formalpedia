-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_293
-- name    : FiniteTriangular.sum_range_293
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:07.288459+00:00
-- url     : https://prove2.me/theorems/2623c6af-da40-47ed-8dcd-8d5aebcd5c26
-- title:
--   Sum of integers below 293
-- statement:
--   The sum of the nonnegative integers strictly less than $293$ equals $42778$. Equivalently, $\\sum_{k=0}^{293-1} k = 293(293-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_293 : ∑ k ∈ range 293, k = 42778 := by sorry

end FiniteTriangular
