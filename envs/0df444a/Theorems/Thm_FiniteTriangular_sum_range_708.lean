-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_708
-- name    : FiniteTriangular.sum_range_708
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:47.106673+00:00
-- url     : https://prove2.me/theorems/98afce27-9783-4d86-8b89-aba65a041408
-- title:
--   Sum of integers below 708
-- statement:
--   The sum of the nonnegative integers strictly less than $708$ equals $250278$. Equivalently, $\\sum_{k=0}^{708-1} k = 708(708-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_708 : ∑ k ∈ range 708, k = 250278 := by sorry

end FiniteTriangular
