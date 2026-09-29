-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_439
-- name    : FiniteTriangular.sum_range_439
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:25.790706+00:00
-- url     : https://prove2.me/theorems/eee482f1-bed4-44d7-a355-ac4044c9d7ae
-- title:
--   Sum of integers below 439
-- statement:
--   The sum of the nonnegative integers strictly less than $439$ equals $96141$. Equivalently, $\\sum_{k=0}^{439-1} k = 439(439-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_439 : ∑ k ∈ range 439, k = 96141 := by sorry

end FiniteTriangular
