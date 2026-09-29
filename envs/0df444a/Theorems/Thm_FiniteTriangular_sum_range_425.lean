-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_425
-- name    : FiniteTriangular.sum_range_425
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:41.783401+00:00
-- url     : https://prove2.me/theorems/a6e870d0-8af5-4ead-88f9-75964f783402
-- title:
--   Sum of integers below 425
-- statement:
--   The sum of the nonnegative integers strictly less than $425$ equals $90100$. Equivalently, $\\sum_{k=0}^{425-1} k = 425(425-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_425 : ∑ k ∈ range 425, k = 90100 := by sorry

end FiniteTriangular
