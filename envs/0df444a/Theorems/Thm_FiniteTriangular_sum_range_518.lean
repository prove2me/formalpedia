-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_518
-- name    : FiniteTriangular.sum_range_518
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:53.249029+00:00
-- url     : https://prove2.me/theorems/98639c33-e65c-4fcd-9edf-83c0290fd690
-- title:
--   Sum of integers below 518
-- statement:
--   The sum of the nonnegative integers strictly less than $518$ equals $133903$. Equivalently, $\\sum_{k=0}^{518-1} k = 518(518-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_518 : ∑ k ∈ range 518, k = 133903 := by sorry

end FiniteTriangular
