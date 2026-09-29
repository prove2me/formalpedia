-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_668
-- name    : FiniteTriangular.sum_range_668
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:13.886128+00:00
-- url     : https://prove2.me/theorems/45e518a8-4de3-4ee1-a932-baf160097b5e
-- title:
--   Sum of integers below 668
-- statement:
--   The sum of the nonnegative integers strictly less than $668$ equals $222778$. Equivalently, $\\sum_{k=0}^{668-1} k = 668(668-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_668 : ∑ k ∈ range 668, k = 222778 := by sorry

end FiniteTriangular
