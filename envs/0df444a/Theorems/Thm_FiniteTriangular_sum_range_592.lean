-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_592
-- name    : FiniteTriangular.sum_range_592
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:22.656492+00:00
-- url     : https://prove2.me/theorems/c55d5403-f69c-4ce8-890f-cf6c63c9bc29
-- title:
--   Sum of integers below 592
-- statement:
--   The sum of the nonnegative integers strictly less than $592$ equals $174936$. Equivalently, $\\sum_{k=0}^{592-1} k = 592(592-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_592 : ∑ k ∈ range 592, k = 174936 := by sorry

end FiniteTriangular
