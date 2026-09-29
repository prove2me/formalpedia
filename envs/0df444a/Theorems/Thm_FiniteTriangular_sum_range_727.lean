-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_727
-- name    : FiniteTriangular.sum_range_727
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:49.735991+00:00
-- url     : https://prove2.me/theorems/4bd5f9d3-53ff-4891-9bdd-841707a930ba
-- title:
--   Sum of integers below 727
-- statement:
--   The sum of the nonnegative integers strictly less than $727$ equals $263901$. Equivalently, $\\sum_{k=0}^{727-1} k = 727(727-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_727 : ∑ k ∈ range 727, k = 263901 := by sorry

end FiniteTriangular
