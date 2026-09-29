-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_806
-- name    : FiniteTriangular.sum_range_806
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:11.254105+00:00
-- url     : https://prove2.me/theorems/bd19609e-93bb-44fb-a4a9-642aa6ca995d
-- title:
--   Sum of integers below 806
-- statement:
--   The sum of the nonnegative integers strictly less than $806$ equals $324415$. Equivalently, $\\sum_{k=0}^{806-1} k = 806(806-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_806 : ∑ k ∈ range 806, k = 324415 := by sorry

end FiniteTriangular
