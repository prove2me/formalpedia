-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_454
-- name    : FiniteTriangular.sum_range_454
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:51.309056+00:00
-- url     : https://prove2.me/theorems/0d62bedd-abc3-4349-b398-be8566b86d6d
-- title:
--   Sum of integers below 454
-- statement:
--   The sum of the nonnegative integers strictly less than $454$ equals $102831$. Equivalently, $\\sum_{k=0}^{454-1} k = 454(454-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_454 : ∑ k ∈ range 454, k = 102831 := by sorry

end FiniteTriangular
