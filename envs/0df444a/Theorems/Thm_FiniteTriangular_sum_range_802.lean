-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_802
-- name    : FiniteTriangular.sum_range_802
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:08.65702+00:00
-- url     : https://prove2.me/theorems/55922e7f-18bd-4fd8-b7bc-0439ec355e4c
-- title:
--   Sum of integers below 802
-- statement:
--   The sum of the nonnegative integers strictly less than $802$ equals $321201$. Equivalently, $\\sum_{k=0}^{802-1} k = 802(802-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_802 : ∑ k ∈ range 802, k = 321201 := by sorry

end FiniteTriangular
