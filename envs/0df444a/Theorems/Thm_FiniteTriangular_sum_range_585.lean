-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_585
-- name    : FiniteTriangular.sum_range_585
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:21.097416+00:00
-- url     : https://prove2.me/theorems/1a90f92d-6281-4c71-ba81-947edf7f667b
-- title:
--   Sum of integers below 585
-- statement:
--   The sum of the nonnegative integers strictly less than $585$ equals $170820$. Equivalently, $\\sum_{k=0}^{585-1} k = 585(585-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_585 : ∑ k ∈ range 585, k = 170820 := by sorry

end FiniteTriangular
