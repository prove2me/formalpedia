-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_272
-- name    : FiniteTriangular.sum_range_272
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:51.853985+00:00
-- url     : https://prove2.me/theorems/db769428-5ed3-42a2-b5dc-d8678e4377f3
-- title:
--   Sum of integers below 272
-- statement:
--   The sum of the nonnegative integers strictly less than $272$ equals $36856$. Equivalently, $\\sum_{k=0}^{272-1} k = 272(272-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_272 : ∑ k ∈ range 272, k = 36856 := by sorry

end FiniteTriangular
