-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_341
-- name    : FiniteTriangular.sum_range_341
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:52.858911+00:00
-- url     : https://prove2.me/theorems/41dc50ba-f1d3-48c4-b0f7-de34fb1d84d6
-- title:
--   Sum of integers below 341
-- statement:
--   The sum of the nonnegative integers strictly less than $341$ equals $57970$. Equivalently, $\\sum_{k=0}^{341-1} k = 341(341-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_341 : ∑ k ∈ range 341, k = 57970 := by sorry

end FiniteTriangular
