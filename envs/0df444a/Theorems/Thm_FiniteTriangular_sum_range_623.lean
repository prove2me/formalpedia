-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_623
-- name    : FiniteTriangular.sum_range_623
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:11.498141+00:00
-- url     : https://prove2.me/theorems/73859f5f-2702-4f85-a89a-96fc5d3e7137
-- title:
--   Sum of integers below 623
-- statement:
--   The sum of the nonnegative integers strictly less than $623$ equals $193753$. Equivalently, $\\sum_{k=0}^{623-1} k = 623(623-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_623 : ∑ k ∈ range 623, k = 193753 := by sorry

end FiniteTriangular
