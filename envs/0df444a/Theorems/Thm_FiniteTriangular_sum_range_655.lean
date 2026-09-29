-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_655
-- name    : FiniteTriangular.sum_range_655
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:50.217059+00:00
-- url     : https://prove2.me/theorems/8eae2475-77d1-4c31-a76d-b75845d99055
-- title:
--   Sum of integers below 655
-- statement:
--   The sum of the nonnegative integers strictly less than $655$ equals $214185$. Equivalently, $\\sum_{k=0}^{655-1} k = 655(655-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_655 : ∑ k ∈ range 655, k = 214185 := by sorry

end FiniteTriangular
