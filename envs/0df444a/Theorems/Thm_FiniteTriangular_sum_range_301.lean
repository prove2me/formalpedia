-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_301
-- name    : FiniteTriangular.sum_range_301
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:55.041434+00:00
-- url     : https://prove2.me/theorems/c123ddc5-07b8-422f-80b4-35b2330b7d1e
-- title:
--   Sum of integers below 301
-- statement:
--   The sum of the nonnegative integers strictly less than $301$ equals $45150$. Equivalently, $\\sum_{k=0}^{301-1} k = 301(301-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_301 : ∑ k ∈ range 301, k = 45150 := by sorry

end FiniteTriangular
