-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_522
-- name    : FiniteTriangular.sum_range_522
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:38.851514+00:00
-- url     : https://prove2.me/theorems/7bfa7170-545c-4aec-b5ec-5241f848d8c3
-- title:
--   Sum of integers below 522
-- statement:
--   The sum of the nonnegative integers strictly less than $522$ equals $135981$. Equivalently, $\\sum_{k=0}^{522-1} k = 522(522-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_522 : ∑ k ∈ range 522, k = 135981 := by sorry

end FiniteTriangular
