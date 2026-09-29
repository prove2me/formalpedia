-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_356
-- name    : FiniteTriangular.sum_range_356
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:16.469292+00:00
-- url     : https://prove2.me/theorems/c2b35ea9-5653-4355-9ba3-545d239f9150
-- title:
--   Sum of integers below 356
-- statement:
--   The sum of the nonnegative integers strictly less than $356$ equals $63190$. Equivalently, $\\sum_{k=0}^{356-1} k = 356(356-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_356 : ∑ k ∈ range 356, k = 63190 := by sorry

end FiniteTriangular
