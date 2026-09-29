-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_733
-- name    : FiniteTriangular.sum_range_733
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:33.671699+00:00
-- url     : https://prove2.me/theorems/0eb42d71-8801-40d2-8344-56a81ccd860c
-- title:
--   Sum of integers below 733
-- statement:
--   The sum of the nonnegative integers strictly less than $733$ equals $268278$. Equivalently, $\\sum_{k=0}^{733-1} k = 733(733-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_733 : ∑ k ∈ range 733, k = 268278 := by sorry

end FiniteTriangular
