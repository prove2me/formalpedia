-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_15
-- name    : FiniteTriangular.sum_range_15
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:03:59.179983+00:00
-- url     : https://prove2.me/theorems/1b82313c-b13a-4006-b192-1c42d4dd4d5d
-- title:
--   Sum of integers below 15
-- statement:
--   The sum of the nonnegative integers strictly less than $15$ equals $105$. Equivalently, $\sum_{k=0}^{15-1} k = 15(15-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_15 : ∑ k ∈ range 15, k = 105 := by sorry

end FiniteTriangular
