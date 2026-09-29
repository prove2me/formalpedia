-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_918
-- name    : FiniteTriangular.sum_range_918
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:49.262046+00:00
-- url     : https://prove2.me/theorems/0dfe661a-856f-4ca2-87ba-ced9b06c1636
-- title:
--   Sum of integers below 918
-- statement:
--   The sum of the nonnegative integers strictly less than $918$ equals $420903$. Equivalently, $\\sum_{k=0}^{918-1} k = 918(918-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_918 : ∑ k ∈ range 918, k = 420903 := by sorry

end FiniteTriangular
