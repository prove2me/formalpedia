-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_342
-- name    : FiniteTriangular.sum_range_342
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:54.592756+00:00
-- url     : https://prove2.me/theorems/d818dfd9-87df-43f4-9748-365b4484e393
-- title:
--   Sum of integers below 342
-- statement:
--   The sum of the nonnegative integers strictly less than $342$ equals $58311$. Equivalently, $\\sum_{k=0}^{342-1} k = 342(342-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_342 : ∑ k ∈ range 342, k = 58311 := by sorry

end FiniteTriangular
