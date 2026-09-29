-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_225
-- name    : FiniteTriangular.sum_range_225
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:00.172551+00:00
-- url     : https://prove2.me/theorems/d4b42b1c-1b6c-4cda-83a8-ad503b09b08a
-- title:
--   Sum of integers below 225
-- statement:
--   The sum of the nonnegative integers strictly less than $225$ equals $25200$. Equivalently, $\\sum_{k=0}^{225-1} k = 225(225-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_225 : ∑ k ∈ range 225, k = 25200 := by sorry

end FiniteTriangular
