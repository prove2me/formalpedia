-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_330
-- name    : FiniteTriangular.sum_range_330
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:06.520125+00:00
-- url     : https://prove2.me/theorems/d79c9822-ac6f-4b31-a409-a8353d35010f
-- title:
--   Sum of integers below 330
-- statement:
--   The sum of the nonnegative integers strictly less than $330$ equals $54285$. Equivalently, $\\sum_{k=0}^{330-1} k = 330(330-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_330 : ∑ k ∈ range 330, k = 54285 := by sorry

end FiniteTriangular
