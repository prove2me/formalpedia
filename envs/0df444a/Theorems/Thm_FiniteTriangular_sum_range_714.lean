-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_714
-- name    : FiniteTriangular.sum_range_714
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:40.528159+00:00
-- url     : https://prove2.me/theorems/93d950a0-3722-49dc-b489-0c3c06e3f17e
-- title:
--   Sum of integers below 714
-- statement:
--   The sum of the nonnegative integers strictly less than $714$ equals $254541$. Equivalently, $\\sum_{k=0}^{714-1} k = 714(714-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_714 : ∑ k ∈ range 714, k = 254541 := by sorry

end FiniteTriangular
