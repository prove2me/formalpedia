-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_442
-- name    : FiniteTriangular.sum_range_442
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:05.757896+00:00
-- url     : https://prove2.me/theorems/10871ca2-9f81-4eb7-9e86-9fba048d0eb4
-- title:
--   Sum of integers below 442
-- statement:
--   The sum of the nonnegative integers strictly less than $442$ equals $97461$. Equivalently, $\\sum_{k=0}^{442-1} k = 442(442-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_442 : ∑ k ∈ range 442, k = 97461 := by sorry

end FiniteTriangular
