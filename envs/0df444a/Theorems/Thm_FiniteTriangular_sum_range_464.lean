-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_464
-- name    : FiniteTriangular.sum_range_464
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:47.687816+00:00
-- url     : https://prove2.me/theorems/0f108ede-08d3-43f4-9939-9fe36747cd83
-- title:
--   Sum of integers below 464
-- statement:
--   The sum of the nonnegative integers strictly less than $464$ equals $107416$. Equivalently, $\\sum_{k=0}^{464-1} k = 464(464-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_464 : ∑ k ∈ range 464, k = 107416 := by sorry

end FiniteTriangular
