-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_466
-- name    : FiniteTriangular.sum_range_466
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:42.902542+00:00
-- url     : https://prove2.me/theorems/a97fdf85-c715-4497-8b62-0956902cdd8b
-- title:
--   Sum of integers below 466
-- statement:
--   The sum of the nonnegative integers strictly less than $466$ equals $108345$. Equivalently, $\\sum_{k=0}^{466-1} k = 466(466-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_466 : ∑ k ∈ range 466, k = 108345 := by sorry

end FiniteTriangular
