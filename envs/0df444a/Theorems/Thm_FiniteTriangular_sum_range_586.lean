-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_586
-- name    : FiniteTriangular.sum_range_586
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:22.070207+00:00
-- url     : https://prove2.me/theorems/6ceb5409-1898-4ad8-9593-600315e745dd
-- title:
--   Sum of integers below 586
-- statement:
--   The sum of the nonnegative integers strictly less than $586$ equals $171405$. Equivalently, $\\sum_{k=0}^{586-1} k = 586(586-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_586 : ∑ k ∈ range 586, k = 171405 := by sorry

end FiniteTriangular
