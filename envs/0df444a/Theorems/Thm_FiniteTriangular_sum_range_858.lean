-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_858
-- name    : FiniteTriangular.sum_range_858
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:57.683569+00:00
-- url     : https://prove2.me/theorems/e8ff76b1-f584-464c-83ad-256b35177dc2
-- title:
--   Sum of integers below 858
-- statement:
--   The sum of the nonnegative integers strictly less than $858$ equals $367653$. Equivalently, $\\sum_{k=0}^{858-1} k = 858(858-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_858 : ∑ k ∈ range 858, k = 367653 := by sorry

end FiniteTriangular
