-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_271
-- name    : FiniteTriangular.sum_range_271
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:47.490127+00:00
-- url     : https://prove2.me/theorems/a7806e79-90bf-4f93-a299-3b98bc5d768e
-- title:
--   Sum of integers below 271
-- statement:
--   The sum of the nonnegative integers strictly less than $271$ equals $36585$. Equivalently, $\\sum_{k=0}^{271-1} k = 271(271-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_271 : ∑ k ∈ range 271, k = 36585 := by sorry

end FiniteTriangular
