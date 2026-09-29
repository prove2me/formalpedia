-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_197
-- name    : FiniteTriangular.sum_range_197
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:21.662321+00:00
-- url     : https://prove2.me/theorems/f4c12d71-2b2b-45c2-8bea-e77e0c9f8f99
-- title:
--   Sum of integers below 197
-- statement:
--   The sum of the nonnegative integers strictly less than $197$ equals $19306$. Equivalently, $\\sum_{k=0}^{197-1} k = 197(197-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_197 : ∑ k ∈ range 197, k = 19306 := by sorry

end FiniteTriangular
