-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_289
-- name    : FiniteTriangular.sum_range_289
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:06.34008+00:00
-- url     : https://prove2.me/theorems/3e1c83c5-8cf8-4c9d-aaac-88e414272a38
-- title:
--   Sum of integers below 289
-- statement:
--   The sum of the nonnegative integers strictly less than $289$ equals $41616$. Equivalently, $\\sum_{k=0}^{289-1} k = 289(289-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_289 : ∑ k ∈ range 289, k = 41616 := by sorry

end FiniteTriangular
