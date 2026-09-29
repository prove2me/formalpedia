-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_815
-- name    : FiniteTriangular.sum_range_815
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:54.446114+00:00
-- url     : https://prove2.me/theorems/2b6c72c3-be46-4b22-9187-03242821f34c
-- title:
--   Sum of integers below 815
-- statement:
--   The sum of the nonnegative integers strictly less than $815$ equals $331705$. Equivalently, $\\sum_{k=0}^{815-1} k = 815(815-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_815 : ∑ k ∈ range 815, k = 331705 := by sorry

end FiniteTriangular
