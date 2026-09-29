-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_492
-- name    : FiniteTriangular.sum_range_492
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:45.071325+00:00
-- url     : https://prove2.me/theorems/32ee1968-6c61-4a94-b669-f6fdf82c6761
-- title:
--   Sum of integers below 492
-- statement:
--   The sum of the nonnegative integers strictly less than $492$ equals $120786$. Equivalently, $\\sum_{k=0}^{492-1} k = 492(492-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_492 : ∑ k ∈ range 492, k = 120786 := by sorry

end FiniteTriangular
