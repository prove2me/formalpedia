-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_210
-- name    : FiniteTriangular.sum_range_210
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:32.947479+00:00
-- url     : https://prove2.me/theorems/e34224cb-e4a4-4136-b13d-27af2375b755
-- title:
--   Sum of integers below 210
-- statement:
--   The sum of the nonnegative integers strictly less than $210$ equals $21945$. Equivalently, $\\sum_{k=0}^{210-1} k = 210(210-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_210 : ∑ k ∈ range 210, k = 21945 := by sorry

end FiniteTriangular
