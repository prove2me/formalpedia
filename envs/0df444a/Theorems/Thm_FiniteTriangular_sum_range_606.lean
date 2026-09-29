-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_606
-- name    : FiniteTriangular.sum_range_606
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:43.611871+00:00
-- url     : https://prove2.me/theorems/b373203a-c46b-4596-b9d3-a63146e22c3a
-- title:
--   Sum of integers below 606
-- statement:
--   The sum of the nonnegative integers strictly less than $606$ equals $183315$. Equivalently, $\\sum_{k=0}^{606-1} k = 606(606-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_606 : ∑ k ∈ range 606, k = 183315 := by sorry

end FiniteTriangular
