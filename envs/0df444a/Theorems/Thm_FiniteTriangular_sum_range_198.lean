-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_198
-- name    : FiniteTriangular.sum_range_198
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:26.020932+00:00
-- url     : https://prove2.me/theorems/b7109027-9c0f-4694-8300-fe61b7a283e0
-- title:
--   Sum of integers below 198
-- statement:
--   The sum of the nonnegative integers strictly less than $198$ equals $19503$. Equivalently, $\\sum_{k=0}^{198-1} k = 198(198-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_198 : ∑ k ∈ range 198, k = 19503 := by sorry

end FiniteTriangular
