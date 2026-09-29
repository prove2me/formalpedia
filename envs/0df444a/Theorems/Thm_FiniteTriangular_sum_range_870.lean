-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_870
-- name    : FiniteTriangular.sum_range_870
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:45.729252+00:00
-- url     : https://prove2.me/theorems/224a2f31-f2d7-4487-9b04-f5c7349f9777
-- title:
--   Sum of integers below 870
-- statement:
--   The sum of the nonnegative integers strictly less than $870$ equals $378015$. Equivalently, $\\sum_{k=0}^{870-1} k = 870(870-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_870 : ∑ k ∈ range 870, k = 378015 := by sorry

end FiniteTriangular
