-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_279
-- name    : FiniteTriangular.sum_range_279
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:43.746189+00:00
-- url     : https://prove2.me/theorems/b885ced0-5976-4e64-84ae-5eb7f49e245e
-- title:
--   Sum of integers below 279
-- statement:
--   The sum of the nonnegative integers strictly less than $279$ equals $38781$. Equivalently, $\\sum_{k=0}^{279-1} k = 279(279-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_279 : ∑ k ∈ range 279, k = 38781 := by sorry

end FiniteTriangular
