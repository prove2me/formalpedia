-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_358
-- name    : FiniteTriangular.sum_range_358
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:19.900481+00:00
-- url     : https://prove2.me/theorems/61e6c3c0-c106-42f1-8c61-922cabac1b0c
-- title:
--   Sum of integers below 358
-- statement:
--   The sum of the nonnegative integers strictly less than $358$ equals $63903$. Equivalently, $\\sum_{k=0}^{358-1} k = 358(358-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_358 : ∑ k ∈ range 358, k = 63903 := by sorry

end FiniteTriangular
