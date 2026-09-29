-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_602
-- name    : FiniteTriangular.sum_range_602
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:44.817646+00:00
-- url     : https://prove2.me/theorems/c05c5d80-33fc-4c22-988b-9e867cf46fe4
-- title:
--   Sum of integers below 602
-- statement:
--   The sum of the nonnegative integers strictly less than $602$ equals $180901$. Equivalently, $\\sum_{k=0}^{602-1} k = 602(602-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_602 : ∑ k ∈ range 602, k = 180901 := by sorry

end FiniteTriangular
