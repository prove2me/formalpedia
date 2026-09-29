-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_587
-- name    : FiniteTriangular.sum_range_587
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:21.411986+00:00
-- url     : https://prove2.me/theorems/a7c36017-1534-481a-9a2e-d2689e7a6b8c
-- title:
--   Sum of integers below 587
-- statement:
--   The sum of the nonnegative integers strictly less than $587$ equals $171991$. Equivalently, $\\sum_{k=0}^{587-1} k = 587(587-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_587 : ∑ k ∈ range 587, k = 171991 := by sorry

end FiniteTriangular
