-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_449
-- name    : FiniteTriangular.sum_range_449
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:51.58762+00:00
-- url     : https://prove2.me/theorems/8d2c1617-6a8e-4f5c-ae7b-be0daae7a769
-- title:
--   Sum of integers below 449
-- statement:
--   The sum of the nonnegative integers strictly less than $449$ equals $100576$. Equivalently, $\\sum_{k=0}^{449-1} k = 449(449-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_449 : ∑ k ∈ range 449, k = 100576 := by sorry

end FiniteTriangular
