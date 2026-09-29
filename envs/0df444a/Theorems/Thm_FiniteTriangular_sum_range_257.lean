-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_257
-- name    : FiniteTriangular.sum_range_257
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:01.513548+00:00
-- url     : https://prove2.me/theorems/5e32ee1e-0214-42b1-ae7c-5531be8ca94b
-- title:
--   Sum of integers below 257
-- statement:
--   The sum of the nonnegative integers strictly less than $257$ equals $32896$. Equivalently, $\\sum_{k=0}^{257-1} k = 257(257-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_257 : ∑ k ∈ range 257, k = 32896 := by sorry

end FiniteTriangular
