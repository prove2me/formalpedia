-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_638
-- name    : FiniteTriangular.sum_range_638
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:40.450082+00:00
-- url     : https://prove2.me/theorems/66103227-c986-4d17-bf8c-4a16f05b99c7
-- title:
--   Sum of integers below 638
-- statement:
--   The sum of the nonnegative integers strictly less than $638$ equals $203203$. Equivalently, $\\sum_{k=0}^{638-1} k = 638(638-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_638 : ∑ k ∈ range 638, k = 203203 := by sorry

end FiniteTriangular
