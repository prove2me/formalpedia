-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_650
-- name    : FiniteTriangular.sum_range_650
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:49.971106+00:00
-- url     : https://prove2.me/theorems/c2623ce3-757f-409c-b4a7-258a58e7083f
-- title:
--   Sum of integers below 650
-- statement:
--   The sum of the nonnegative integers strictly less than $650$ equals $210925$. Equivalently, $\\sum_{k=0}^{650-1} k = 650(650-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_650 : ∑ k ∈ range 650, k = 210925 := by sorry

end FiniteTriangular
