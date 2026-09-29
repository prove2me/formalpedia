-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_817
-- name    : FiniteTriangular.sum_range_817
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:44.740767+00:00
-- url     : https://prove2.me/theorems/8060bbc7-46a0-4d29-8283-725396e8815e
-- title:
--   Sum of integers below 817
-- statement:
--   The sum of the nonnegative integers strictly less than $817$ equals $333336$. Equivalently, $\\sum_{k=0}^{817-1} k = 817(817-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_817 : ∑ k ∈ range 817, k = 333336 := by sorry

end FiniteTriangular
