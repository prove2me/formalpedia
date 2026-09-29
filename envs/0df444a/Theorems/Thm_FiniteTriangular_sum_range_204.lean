-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_204
-- name    : FiniteTriangular.sum_range_204
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:22.866394+00:00
-- url     : https://prove2.me/theorems/ad6232de-00cb-4c61-9bec-c6fef73ab5b8
-- title:
--   Sum of integers below 204
-- statement:
--   The sum of the nonnegative integers strictly less than $204$ equals $20706$. Equivalently, $\\sum_{k=0}^{204-1} k = 204(204-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_204 : ∑ k ∈ range 204, k = 20706 := by sorry

end FiniteTriangular
