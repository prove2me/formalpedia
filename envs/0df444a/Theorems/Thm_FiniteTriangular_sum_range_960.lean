-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_960
-- name    : FiniteTriangular.sum_range_960
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:47.90253+00:00
-- url     : https://prove2.me/theorems/320dad77-cb1d-447c-9bc0-0240bd8480bd
-- title:
--   Sum of integers below 960
-- statement:
--   The sum of the nonnegative integers strictly less than $960$ equals $460320$. Equivalently, $\\sum_{k=0}^{960-1} k = 960(960-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_960 : ∑ k ∈ range 960, k = 460320 := by sorry

end FiniteTriangular
