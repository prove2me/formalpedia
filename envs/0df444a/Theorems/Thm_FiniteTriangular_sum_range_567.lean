-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_567
-- name    : FiniteTriangular.sum_range_567
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:07.41879+00:00
-- url     : https://prove2.me/theorems/90154d89-a0f1-419d-92f1-37186bc0c6f9
-- title:
--   Sum of integers below 567
-- statement:
--   The sum of the nonnegative integers strictly less than $567$ equals $160461$. Equivalently, $\\sum_{k=0}^{567-1} k = 567(567-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_567 : ∑ k ∈ range 567, k = 160461 := by sorry

end FiniteTriangular
