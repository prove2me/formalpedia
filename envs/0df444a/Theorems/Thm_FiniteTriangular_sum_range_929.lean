-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_929
-- name    : FiniteTriangular.sum_range_929
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:13.565393+00:00
-- url     : https://prove2.me/theorems/c5a7d32b-dc00-4146-8eb7-b38ac24efc78
-- title:
--   Sum of integers below 929
-- statement:
--   The sum of the nonnegative integers strictly less than $929$ equals $431056$. Equivalently, $\\sum_{k=0}^{929-1} k = 929(929-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_929 : ∑ k ∈ range 929, k = 431056 := by sorry

end FiniteTriangular
