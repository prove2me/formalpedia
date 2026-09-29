-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_955
-- name    : FiniteTriangular.sum_range_955
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:46.660747+00:00
-- url     : https://prove2.me/theorems/ae924e06-fe4e-4b69-b476-ebbdf1da6a6f
-- title:
--   Sum of integers below 955
-- statement:
--   The sum of the nonnegative integers strictly less than $955$ equals $455535$. Equivalently, $\\sum_{k=0}^{955-1} k = 955(955-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_955 : ∑ k ∈ range 955, k = 455535 := by sorry

end FiniteTriangular
