-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_540
-- name    : FiniteTriangular.sum_range_540
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:54.735961+00:00
-- url     : https://prove2.me/theorems/5d93c5a0-28b7-4d4e-a49f-b100ee128faf
-- title:
--   Sum of integers below 540
-- statement:
--   The sum of the nonnegative integers strictly less than $540$ equals $145530$. Equivalently, $\\sum_{k=0}^{540-1} k = 540(540-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_540 : ∑ k ∈ range 540, k = 145530 := by sorry

end FiniteTriangular
