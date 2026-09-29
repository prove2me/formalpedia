-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_418
-- name    : FiniteTriangular.sum_range_418
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:54.016331+00:00
-- url     : https://prove2.me/theorems/ad138ca0-25d3-462a-bed4-ab9518726b0d
-- title:
--   Sum of integers below 418
-- statement:
--   The sum of the nonnegative integers strictly less than $418$ equals $87153$. Equivalently, $\\sum_{k=0}^{418-1} k = 418(418-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_418 : ∑ k ∈ range 418, k = 87153 := by sorry

end FiniteTriangular
