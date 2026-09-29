-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_915
-- name    : FiniteTriangular.sum_range_915
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:48.593995+00:00
-- url     : https://prove2.me/theorems/010203d9-7e51-42ef-9631-10447f3a4f6d
-- title:
--   Sum of integers below 915
-- statement:
--   The sum of the nonnegative integers strictly less than $915$ equals $418155$. Equivalently, $\\sum_{k=0}^{915-1} k = 915(915-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_915 : ∑ k ∈ range 915, k = 418155 := by sorry

end FiniteTriangular
