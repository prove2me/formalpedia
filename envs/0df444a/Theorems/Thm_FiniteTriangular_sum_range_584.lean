-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_584
-- name    : FiniteTriangular.sum_range_584
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:36.754434+00:00
-- url     : https://prove2.me/theorems/32b7da26-d726-4aab-85a7-1b69cfa9694b
-- title:
--   Sum of integers below 584
-- statement:
--   The sum of the nonnegative integers strictly less than $584$ equals $170236$. Equivalently, $\\sum_{k=0}^{584-1} k = 584(584-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_584 : ∑ k ∈ range 584, k = 170236 := by sorry

end FiniteTriangular
