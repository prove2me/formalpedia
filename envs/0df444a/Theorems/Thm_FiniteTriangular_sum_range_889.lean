-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_889
-- name    : FiniteTriangular.sum_range_889
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:54.041586+00:00
-- url     : https://prove2.me/theorems/f0885db9-7a8c-45da-ac41-35c84b28285b
-- title:
--   Sum of integers below 889
-- statement:
--   The sum of the nonnegative integers strictly less than $889$ equals $394716$. Equivalently, $\\sum_{k=0}^{889-1} k = 889(889-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_889 : ∑ k ∈ range 889, k = 394716 := by sorry

end FiniteTriangular
