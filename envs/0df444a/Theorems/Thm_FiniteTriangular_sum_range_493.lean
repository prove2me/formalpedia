-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_493
-- name    : FiniteTriangular.sum_range_493
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:46.065349+00:00
-- url     : https://prove2.me/theorems/56897031-06db-4dd5-b815-ef5fc3c58652
-- title:
--   Sum of integers below 493
-- statement:
--   The sum of the nonnegative integers strictly less than $493$ equals $121278$. Equivalently, $\\sum_{k=0}^{493-1} k = 493(493-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_493 : ∑ k ∈ range 493, k = 121278 := by sorry

end FiniteTriangular
