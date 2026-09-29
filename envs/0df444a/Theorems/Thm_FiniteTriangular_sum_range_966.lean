-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_966
-- name    : FiniteTriangular.sum_range_966
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:34.97662+00:00
-- url     : https://prove2.me/theorems/035afb4f-b233-4d34-bc12-f43258935b14
-- title:
--   Sum of integers below 966
-- statement:
--   The sum of the nonnegative integers strictly less than $966$ equals $466095$. Equivalently, $\\sum_{k=0}^{966-1} k = 966(966-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_966 : ∑ k ∈ range 966, k = 466095 := by sorry

end FiniteTriangular
