-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_427
-- name    : FiniteTriangular.sum_range_427
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:39.853734+00:00
-- url     : https://prove2.me/theorems/11bf0afe-67a5-4c3a-9c2a-9c28db0dbb18
-- title:
--   Sum of integers below 427
-- statement:
--   The sum of the nonnegative integers strictly less than $427$ equals $90951$. Equivalently, $\\sum_{k=0}^{427-1} k = 427(427-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_427 : ∑ k ∈ range 427, k = 90951 := by sorry

end FiniteTriangular
