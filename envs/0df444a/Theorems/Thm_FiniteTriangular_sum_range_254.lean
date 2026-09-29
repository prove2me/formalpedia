-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_254
-- name    : FiniteTriangular.sum_range_254
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:05.468954+00:00
-- url     : https://prove2.me/theorems/5e2d6595-9426-4e56-9045-70f9509d8f39
-- title:
--   Sum of integers below 254
-- statement:
--   The sum of the nonnegative integers strictly less than $254$ equals $32131$. Equivalently, $\\sum_{k=0}^{254-1} k = 254(254-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_254 : ∑ k ∈ range 254, k = 32131 := by sorry

end FiniteTriangular
