-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_275
-- name    : FiniteTriangular.sum_range_275
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:41.206984+00:00
-- url     : https://prove2.me/theorems/a9be513b-c8e1-47bd-a5db-b893370f5e5c
-- title:
--   Sum of integers below 275
-- statement:
--   The sum of the nonnegative integers strictly less than $275$ equals $37675$. Equivalently, $\\sum_{k=0}^{275-1} k = 275(275-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_275 : ∑ k ∈ range 275, k = 37675 := by sorry

end FiniteTriangular
