-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_305
-- name    : FiniteTriangular.sum_range_305
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:51.168696+00:00
-- url     : https://prove2.me/theorems/23cb614e-b857-4e1a-941c-590d8cdc0c15
-- title:
--   Sum of integers below 305
-- statement:
--   The sum of the nonnegative integers strictly less than $305$ equals $46360$. Equivalently, $\\sum_{k=0}^{305-1} k = 305(305-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_305 : ∑ k ∈ range 305, k = 46360 := by sorry

end FiniteTriangular
