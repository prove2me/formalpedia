-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_844
-- name    : FiniteTriangular.sum_range_844
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:46.778964+00:00
-- url     : https://prove2.me/theorems/94946c5d-7033-4387-a336-0f30ef6ae21f
-- title:
--   Sum of integers below 844
-- statement:
--   The sum of the nonnegative integers strictly less than $844$ equals $355746$. Equivalently, $\\sum_{k=0}^{844-1} k = 844(844-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_844 : ∑ k ∈ range 844, k = 355746 := by sorry

end FiniteTriangular
