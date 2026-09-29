-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_773
-- name    : FiniteTriangular.sum_range_773
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:28.826921+00:00
-- url     : https://prove2.me/theorems/029c446d-0efd-4bb2-b530-55114b799e5f
-- title:
--   Sum of integers below 773
-- statement:
--   The sum of the nonnegative integers strictly less than $773$ equals $298378$. Equivalently, $\\sum_{k=0}^{773-1} k = 773(773-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_773 : ∑ k ∈ range 773, k = 298378 := by sorry

end FiniteTriangular
