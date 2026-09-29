-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_767
-- name    : FiniteTriangular.sum_range_767
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:37.878911+00:00
-- url     : https://prove2.me/theorems/8e3be332-81d0-4702-906f-f6887eb851d6
-- title:
--   Sum of integers below 767
-- statement:
--   The sum of the nonnegative integers strictly less than $767$ equals $293761$. Equivalently, $\\sum_{k=0}^{767-1} k = 767(767-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_767 : ∑ k ∈ range 767, k = 293761 := by sorry

end FiniteTriangular
