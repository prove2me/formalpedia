-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_880
-- name    : FiniteTriangular.sum_range_880
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:30.827805+00:00
-- url     : https://prove2.me/theorems/68eb06a7-e06a-4632-9e7a-7babda0c67e6
-- title:
--   Sum of integers below 880
-- statement:
--   The sum of the nonnegative integers strictly less than $880$ equals $386760$. Equivalently, $\\sum_{k=0}^{880-1} k = 880(880-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_880 : ∑ k ∈ range 880, k = 386760 := by sorry

end FiniteTriangular
