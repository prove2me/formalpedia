-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_579
-- name    : FiniteTriangular.sum_range_579
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:37.816841+00:00
-- url     : https://prove2.me/theorems/e5de4ebb-5539-4db9-9fc2-c36a60811dfe
-- title:
--   Sum of integers below 579
-- statement:
--   The sum of the nonnegative integers strictly less than $579$ equals $167331$. Equivalently, $\\sum_{k=0}^{579-1} k = 579(579-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_579 : ∑ k ∈ range 579, k = 167331 := by sorry

end FiniteTriangular
