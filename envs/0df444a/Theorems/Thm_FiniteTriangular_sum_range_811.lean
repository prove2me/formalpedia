-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_811
-- name    : FiniteTriangular.sum_range_811
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:54.998429+00:00
-- url     : https://prove2.me/theorems/0016e25a-65d9-4e2d-91da-0f819f673551
-- title:
--   Sum of integers below 811
-- statement:
--   The sum of the nonnegative integers strictly less than $811$ equals $328455$. Equivalently, $\\sum_{k=0}^{811-1} k = 811(811-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_811 : ∑ k ∈ range 811, k = 328455 := by sorry

end FiniteTriangular
