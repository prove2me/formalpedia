-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_400
-- name    : FiniteTriangular.sum_range_400
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:44.298803+00:00
-- url     : https://prove2.me/theorems/553e1247-ef3b-4d90-b96f-af71caf6231f
-- title:
--   Sum of integers below 400
-- statement:
--   The sum of the nonnegative integers strictly less than $400$ equals $79800$. Equivalently, $\\sum_{k=0}^{400-1} k = 400(400-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_400 : ∑ k ∈ range 400, k = 79800 := by sorry

end FiniteTriangular
