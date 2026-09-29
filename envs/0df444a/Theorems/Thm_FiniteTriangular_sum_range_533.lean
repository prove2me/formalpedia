-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_533
-- name    : FiniteTriangular.sum_range_533
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:17.602106+00:00
-- url     : https://prove2.me/theorems/207a3b53-f306-41f3-94e3-da7fa9c6f76f
-- title:
--   Sum of integers below 533
-- statement:
--   The sum of the nonnegative integers strictly less than $533$ equals $141778$. Equivalently, $\\sum_{k=0}^{533-1} k = 533(533-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_533 : ∑ k ∈ range 533, k = 141778 := by sorry

end FiniteTriangular
