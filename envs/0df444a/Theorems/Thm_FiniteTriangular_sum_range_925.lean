-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_925
-- name    : FiniteTriangular.sum_range_925
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:34.343461+00:00
-- url     : https://prove2.me/theorems/d0b5c0b7-f093-4692-8b54-266145d16ab4
-- title:
--   Sum of integers below 925
-- statement:
--   The sum of the nonnegative integers strictly less than $925$ equals $427350$. Equivalently, $\\sum_{k=0}^{925-1} k = 925(925-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_925 : ∑ k ∈ range 925, k = 427350 := by sorry

end FiniteTriangular
