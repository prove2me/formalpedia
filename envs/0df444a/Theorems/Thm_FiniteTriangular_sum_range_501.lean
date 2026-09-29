-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_501
-- name    : FiniteTriangular.sum_range_501
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:26.396816+00:00
-- url     : https://prove2.me/theorems/ea7a873f-004b-44df-bde2-77118d89976a
-- title:
--   Sum of integers below 501
-- statement:
--   The sum of the nonnegative integers strictly less than $501$ equals $125250$. Equivalently, $\\sum_{k=0}^{501-1} k = 501(501-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_501 : ∑ k ∈ range 501, k = 125250 := by sorry

end FiniteTriangular
