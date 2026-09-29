-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_519
-- name    : FiniteTriangular.sum_range_519
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:54.303755+00:00
-- url     : https://prove2.me/theorems/52dc3928-f8f5-4891-9c4d-60edd3c5d2c5
-- title:
--   Sum of integers below 519
-- statement:
--   The sum of the nonnegative integers strictly less than $519$ equals $134421$. Equivalently, $\\sum_{k=0}^{519-1} k = 519(519-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_519 : ∑ k ∈ range 519, k = 134421 := by sorry

end FiniteTriangular
