-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_188
-- name    : FiniteTriangular.sum_range_188
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:08.57363+00:00
-- url     : https://prove2.me/theorems/1ccf4193-59e6-4b49-958a-19f5366a5b57
-- title:
--   Sum of integers below 188
-- statement:
--   The sum of the nonnegative integers strictly less than $188$ equals $17578$. Equivalently, $\\sum_{k=0}^{188-1} k = 188(188-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_188 : ∑ k ∈ range 188, k = 17578 := by sorry

end FiniteTriangular
