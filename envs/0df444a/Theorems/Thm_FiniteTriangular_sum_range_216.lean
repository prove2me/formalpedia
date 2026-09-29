-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_216
-- name    : FiniteTriangular.sum_range_216
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:32.273974+00:00
-- url     : https://prove2.me/theorems/8b954e08-9c4b-4efa-afae-d6b88e496ba8
-- title:
--   Sum of integers below 216
-- statement:
--   The sum of the nonnegative integers strictly less than $216$ equals $23220$. Equivalently, $\\sum_{k=0}^{216-1} k = 216(216-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_216 : ∑ k ∈ range 216, k = 23220 := by sorry

end FiniteTriangular
