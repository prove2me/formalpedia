-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_687
-- name    : FiniteTriangular.sum_range_687
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:50.480409+00:00
-- url     : https://prove2.me/theorems/9ec5a2b2-4a25-4cff-a172-a25a6cf795b8
-- title:
--   Sum of integers below 687
-- statement:
--   The sum of the nonnegative integers strictly less than $687$ equals $235641$. Equivalently, $\\sum_{k=0}^{687-1} k = 687(687-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_687 : ∑ k ∈ range 687, k = 235641 := by sorry

end FiniteTriangular
