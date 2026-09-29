-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_274
-- name    : FiniteTriangular.sum_range_274
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:41.206984+00:00
-- url     : https://prove2.me/theorems/7f150498-b468-4b3a-a469-bdddf813c531
-- title:
--   Sum of integers below 274
-- statement:
--   The sum of the nonnegative integers strictly less than $274$ equals $37401$. Equivalently, $\\sum_{k=0}^{274-1} k = 274(274-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_274 : ∑ k ∈ range 274, k = 37401 := by sorry

end FiniteTriangular
