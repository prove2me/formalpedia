-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_390
-- name    : FiniteTriangular.sum_range_390
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:46:57.792986+00:00
-- url     : https://prove2.me/theorems/808553aa-c059-4de0-88c0-3b4609ae1025
-- title:
--   Sum of integers below 390
-- statement:
--   The sum of the nonnegative integers strictly less than $390$ equals $75855$. Equivalently, $\\sum_{k=0}^{390-1} k = 390(390-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_390 : ∑ k ∈ range 390, k = 75855 := by sorry

end FiniteTriangular
