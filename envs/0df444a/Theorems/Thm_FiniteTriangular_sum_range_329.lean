-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_329
-- name    : FiniteTriangular.sum_range_329
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:05.525719+00:00
-- url     : https://prove2.me/theorems/6158d165-d8bb-481a-a798-a08e2d1bac7c
-- title:
--   Sum of integers below 329
-- statement:
--   The sum of the nonnegative integers strictly less than $329$ equals $53956$. Equivalently, $\\sum_{k=0}^{329-1} k = 329(329-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_329 : ∑ k ∈ range 329, k = 53956 := by sorry

end FiniteTriangular
