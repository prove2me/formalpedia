-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_281
-- name    : FiniteTriangular.sum_range_281
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:29.229294+00:00
-- url     : https://prove2.me/theorems/cdfcba53-9004-477b-b450-6a35368e8bd4
-- title:
--   Sum of integers below 281
-- statement:
--   The sum of the nonnegative integers strictly less than $281$ equals $39340$. Equivalently, $\\sum_{k=0}^{281-1} k = 281(281-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_281 : ∑ k ∈ range 281, k = 39340 := by sorry

end FiniteTriangular
