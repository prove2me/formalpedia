-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_350
-- name    : FiniteTriangular.sum_range_350
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:38.277339+00:00
-- url     : https://prove2.me/theorems/1d366f6c-e93e-436a-9ba2-2e7357bc0a55
-- title:
--   Sum of integers below 350
-- statement:
--   The sum of the nonnegative integers strictly less than $350$ equals $61075$. Equivalently, $\\sum_{k=0}^{350-1} k = 350(350-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_350 : ∑ k ∈ range 350, k = 61075 := by sorry

end FiniteTriangular
