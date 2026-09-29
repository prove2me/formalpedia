-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_743
-- name    : FiniteTriangular.sum_range_743
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:31.354824+00:00
-- url     : https://prove2.me/theorems/37108e15-8a12-4cec-b1b2-8ae045f867d4
-- title:
--   Sum of integers below 743
-- statement:
--   The sum of the nonnegative integers strictly less than $743$ equals $275653$. Equivalently, $\\sum_{k=0}^{743-1} k = 743(743-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_743 : ∑ k ∈ range 743, k = 275653 := by sorry

end FiniteTriangular
