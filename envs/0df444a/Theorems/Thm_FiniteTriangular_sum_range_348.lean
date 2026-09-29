-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_348
-- name    : FiniteTriangular.sum_range_348
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:37.590958+00:00
-- url     : https://prove2.me/theorems/1a3a82df-4263-4990-add1-df6678ccc243
-- title:
--   Sum of integers below 348
-- statement:
--   The sum of the nonnegative integers strictly less than $348$ equals $60378$. Equivalently, $\\sum_{k=0}^{348-1} k = 348(348-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_348 : ∑ k ∈ range 348, k = 60378 := by sorry

end FiniteTriangular
