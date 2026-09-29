-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_394
-- name    : FiniteTriangular.sum_range_394
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:42.212088+00:00
-- url     : https://prove2.me/theorems/f8cc89e5-911c-4f82-85b9-843081f1f5c2
-- title:
--   Sum of integers below 394
-- statement:
--   The sum of the nonnegative integers strictly less than $394$ equals $77421$. Equivalently, $\\sum_{k=0}^{394-1} k = 394(394-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_394 : ∑ k ∈ range 394, k = 77421 := by sorry

end FiniteTriangular
