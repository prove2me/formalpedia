-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_526
-- name    : FiniteTriangular.sum_range_526
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:42.050113+00:00
-- url     : https://prove2.me/theorems/c843ac61-d8e5-4f14-960c-6e2b591df483
-- title:
--   Sum of integers below 526
-- statement:
--   The sum of the nonnegative integers strictly less than $526$ equals $138075$. Equivalently, $\\sum_{k=0}^{526-1} k = 526(526-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_526 : ∑ k ∈ range 526, k = 138075 := by sorry

end FiniteTriangular
