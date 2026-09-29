-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_731
-- name    : FiniteTriangular.sum_range_731
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:36.531901+00:00
-- url     : https://prove2.me/theorems/04173d64-50a9-444c-84e4-f86d3b392887
-- title:
--   Sum of integers below 731
-- statement:
--   The sum of the nonnegative integers strictly less than $731$ equals $266815$. Equivalently, $\\sum_{k=0}^{731-1} k = 731(731-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_731 : ∑ k ∈ range 731, k = 266815 := by sorry

end FiniteTriangular
