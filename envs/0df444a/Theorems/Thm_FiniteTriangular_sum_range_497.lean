-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_497
-- name    : FiniteTriangular.sum_range_497
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:25.016504+00:00
-- url     : https://prove2.me/theorems/8c1112a7-d47c-456b-88eb-74da4f7939ce
-- title:
--   Sum of integers below 497
-- statement:
--   The sum of the nonnegative integers strictly less than $497$ equals $123256$. Equivalently, $\\sum_{k=0}^{497-1} k = 497(497-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_497 : ∑ k ∈ range 497, k = 123256 := by sorry

end FiniteTriangular
