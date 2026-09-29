-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_598
-- name    : FiniteTriangular.sum_range_598
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:43:02.188155+00:00
-- url     : https://prove2.me/theorems/32270042-9a6a-46ba-9988-2e258e64fe4c
-- title:
--   Sum of integers below 598
-- statement:
--   The sum of the nonnegative integers strictly less than $598$ equals $178503$. Equivalently, $\\sum_{k=0}^{598-1} k = 598(598-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_598 : ∑ k ∈ range 598, k = 178503 := by sorry

end FiniteTriangular
