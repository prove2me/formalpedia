-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_180
-- name    : FiniteTriangular.sum_range_180
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:03:59.01866+00:00
-- url     : https://prove2.me/theorems/bdf386b3-f967-42a8-9a05-a6e986e950a5
-- title:
--   Sum of integers below 180
-- statement:
--   The sum of the nonnegative integers strictly less than $180$ equals $16110$. Equivalently, $\sum_{k=0}^{180-1} k = 180(180-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_180 : ∑ k ∈ range 180, k = 16110 := by sorry

end FiniteTriangular
