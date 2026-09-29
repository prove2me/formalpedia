-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_461
-- name    : FiniteTriangular.sum_range_461
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:46.802664+00:00
-- url     : https://prove2.me/theorems/87f50a65-7973-4290-82ef-7f4107890382
-- title:
--   Sum of integers below 461
-- statement:
--   The sum of the nonnegative integers strictly less than $461$ equals $106030$. Equivalently, $\\sum_{k=0}^{461-1} k = 461(461-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_461 : ∑ k ∈ range 461, k = 106030 := by sorry

end FiniteTriangular
