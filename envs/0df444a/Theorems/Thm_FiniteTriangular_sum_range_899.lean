-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_899
-- name    : FiniteTriangular.sum_range_899
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:30.58412+00:00
-- url     : https://prove2.me/theorems/df46f2e3-8b61-4052-bfb4-e02b87a323b1
-- title:
--   Sum of integers below 899
-- statement:
--   The sum of the nonnegative integers strictly less than $899$ equals $403651$. Equivalently, $\\sum_{k=0}^{899-1} k = 899(899-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_899 : ∑ k ∈ range 899, k = 403651 := by sorry

end FiniteTriangular
