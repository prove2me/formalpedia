-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_942
-- name    : FiniteTriangular.sum_range_942
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:57:00.160427+00:00
-- url     : https://prove2.me/theorems/024759d0-c05b-4d51-8463-255e6499d1f8
-- title:
--   Sum of integers below 942
-- statement:
--   The sum of the nonnegative integers strictly less than $942$ equals $443211$. Equivalently, $\\sum_{k=0}^{942-1} k = 942(942-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_942 : ∑ k ∈ range 942, k = 443211 := by sorry

end FiniteTriangular
