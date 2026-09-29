-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_862
-- name    : FiniteTriangular.sum_range_862
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:58.487425+00:00
-- url     : https://prove2.me/theorems/3d6507c7-80c9-422e-a11e-1734eaae3e67
-- title:
--   Sum of integers below 862
-- statement:
--   The sum of the nonnegative integers strictly less than $862$ equals $371091$. Equivalently, $\\sum_{k=0}^{862-1} k = 862(862-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_862 : ∑ k ∈ range 862, k = 371091 := by sorry

end FiniteTriangular
