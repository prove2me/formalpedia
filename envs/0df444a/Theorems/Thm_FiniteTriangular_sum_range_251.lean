-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_251
-- name    : FiniteTriangular.sum_range_251
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:06.301661+00:00
-- url     : https://prove2.me/theorems/ec3c9dfd-43ad-4a29-9967-2631a0940bee
-- title:
--   Sum of integers below 251
-- statement:
--   The sum of the nonnegative integers strictly less than $251$ equals $31375$. Equivalently, $\\sum_{k=0}^{251-1} k = 251(251-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_251 : ∑ k ∈ range 251, k = 31375 := by sorry

end FiniteTriangular
