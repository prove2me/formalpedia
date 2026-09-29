-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_550
-- name    : FiniteTriangular.sum_range_550
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:45.680834+00:00
-- url     : https://prove2.me/theorems/a235e1ce-e2c5-4291-a69f-a21ff77f819c
-- title:
--   Sum of integers below 550
-- statement:
--   The sum of the nonnegative integers strictly less than $550$ equals $150975$. Equivalently, $\\sum_{k=0}^{550-1} k = 550(550-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_550 : ∑ k ∈ range 550, k = 150975 := by sorry

end FiniteTriangular
