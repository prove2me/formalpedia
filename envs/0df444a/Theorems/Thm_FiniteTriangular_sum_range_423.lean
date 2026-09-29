-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_423
-- name    : FiniteTriangular.sum_range_423
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:52.401544+00:00
-- url     : https://prove2.me/theorems/47b59fd2-7bde-4f97-aac4-8e84f5d58128
-- title:
--   Sum of integers below 423
-- statement:
--   The sum of the nonnegative integers strictly less than $423$ equals $89253$. Equivalently, $\\sum_{k=0}^{423-1} k = 423(423-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_423 : ∑ k ∈ range 423, k = 89253 := by sorry

end FiniteTriangular
