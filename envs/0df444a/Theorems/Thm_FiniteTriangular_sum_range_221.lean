-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_221
-- name    : FiniteTriangular.sum_range_221
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:15.991694+00:00
-- url     : https://prove2.me/theorems/b457bd1c-d037-47b1-991f-50bd9686abf4
-- title:
--   Sum of integers below 221
-- statement:
--   The sum of the nonnegative integers strictly less than $221$ equals $24310$. Equivalently, $\\sum_{k=0}^{221-1} k = 221(221-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_221 : ∑ k ∈ range 221, k = 24310 := by sorry

end FiniteTriangular
