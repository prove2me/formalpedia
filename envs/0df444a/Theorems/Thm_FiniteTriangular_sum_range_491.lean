-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_491
-- name    : FiniteTriangular.sum_range_491
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:45.969154+00:00
-- url     : https://prove2.me/theorems/7a7fccdc-6376-4dd3-a306-93a8a8fd0d7b
-- title:
--   Sum of integers below 491
-- statement:
--   The sum of the nonnegative integers strictly less than $491$ equals $120295$. Equivalently, $\\sum_{k=0}^{491-1} k = 491(491-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_491 : ∑ k ∈ range 491, k = 120295 := by sorry

end FiniteTriangular
