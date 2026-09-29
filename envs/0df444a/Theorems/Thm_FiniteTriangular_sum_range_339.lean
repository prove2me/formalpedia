-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_339
-- name    : FiniteTriangular.sum_range_339
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:55.38075+00:00
-- url     : https://prove2.me/theorems/478168c5-977d-479b-a324-11b65c46bf21
-- title:
--   Sum of integers below 339
-- statement:
--   The sum of the nonnegative integers strictly less than $339$ equals $57291$. Equivalently, $\\sum_{k=0}^{339-1} k = 339(339-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_339 : ∑ k ∈ range 339, k = 57291 := by sorry

end FiniteTriangular
