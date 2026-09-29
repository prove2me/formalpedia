-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_939
-- name    : FiniteTriangular.sum_range_939
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:56:57.501933+00:00
-- url     : https://prove2.me/theorems/ad2f48a5-3199-4d7a-9e0c-9fa890589daa
-- title:
--   Sum of integers below 939
-- statement:
--   The sum of the nonnegative integers strictly less than $939$ equals $440391$. Equivalently, $\\sum_{k=0}^{939-1} k = 939(939-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_939 : ∑ k ∈ range 939, k = 440391 := by sorry

end FiniteTriangular
