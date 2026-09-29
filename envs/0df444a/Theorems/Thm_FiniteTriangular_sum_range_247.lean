-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_247
-- name    : FiniteTriangular.sum_range_247
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:15.569469+00:00
-- url     : https://prove2.me/theorems/c7c704c7-90ea-427b-9f7e-8ed8cb4d7c0a
-- title:
--   Sum of integers below 247
-- statement:
--   The sum of the nonnegative integers strictly less than $247$ equals $30381$. Equivalently, $\\sum_{k=0}^{247-1} k = 247(247-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_247 : ∑ k ∈ range 247, k = 30381 := by sorry

end FiniteTriangular
