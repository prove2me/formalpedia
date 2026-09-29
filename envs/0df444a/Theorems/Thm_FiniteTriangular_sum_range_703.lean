-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_703
-- name    : FiniteTriangular.sum_range_703
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:58.289164+00:00
-- url     : https://prove2.me/theorems/5df86a63-0b52-4e69-8125-b0161aa558dd
-- title:
--   Sum of integers below 703
-- statement:
--   The sum of the nonnegative integers strictly less than $703$ equals $246753$. Equivalently, $\\sum_{k=0}^{703-1} k = 703(703-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_703 : ∑ k ∈ range 703, k = 246753 := by sorry

end FiniteTriangular
