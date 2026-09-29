-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_583
-- name    : FiniteTriangular.sum_range_583
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:38.221422+00:00
-- url     : https://prove2.me/theorems/c1547450-78f3-47d5-b3d8-93a79b3055b9
-- title:
--   Sum of integers below 583
-- statement:
--   The sum of the nonnegative integers strictly less than $583$ equals $169653$. Equivalently, $\\sum_{k=0}^{583-1} k = 583(583-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_583 : ∑ k ∈ range 583, k = 169653 := by sorry

end FiniteTriangular
