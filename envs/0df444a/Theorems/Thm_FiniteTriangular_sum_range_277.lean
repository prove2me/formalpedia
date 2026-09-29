-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_277
-- name    : FiniteTriangular.sum_range_277
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:43.084964+00:00
-- url     : https://prove2.me/theorems/5ca7e64d-2470-4e10-b0f0-c9367dc2fe60
-- title:
--   Sum of integers below 277
-- statement:
--   The sum of the nonnegative integers strictly less than $277$ equals $38226$. Equivalently, $\\sum_{k=0}^{277-1} k = 277(277-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_277 : ∑ k ∈ range 277, k = 38226 := by sorry

end FiniteTriangular
