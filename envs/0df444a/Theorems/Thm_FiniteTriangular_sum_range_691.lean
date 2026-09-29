-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_691
-- name    : FiniteTriangular.sum_range_691
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:24.20447+00:00
-- url     : https://prove2.me/theorems/17bcc9e6-c3fc-4b40-9f49-53bd91d3a07c
-- title:
--   Sum of integers below 691
-- statement:
--   The sum of the nonnegative integers strictly less than $691$ equals $238395$. Equivalently, $\\sum_{k=0}^{691-1} k = 691(691-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_691 : ∑ k ∈ range 691, k = 238395 := by sorry

end FiniteTriangular
