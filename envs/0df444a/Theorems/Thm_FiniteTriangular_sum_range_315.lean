-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_315
-- name    : FiniteTriangular.sum_range_315
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:27.311924+00:00
-- url     : https://prove2.me/theorems/85d08be4-4efb-47fa-9ad8-7eebb09aedd5
-- title:
--   Sum of integers below 315
-- statement:
--   The sum of the nonnegative integers strictly less than $315$ equals $49455$. Equivalently, $\\sum_{k=0}^{315-1} k = 315(315-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_315 : ∑ k ∈ range 315, k = 49455 := by sorry

end FiniteTriangular
