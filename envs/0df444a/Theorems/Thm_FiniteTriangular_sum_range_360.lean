-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_360
-- name    : FiniteTriangular.sum_range_360
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:17.590557+00:00
-- url     : https://prove2.me/theorems/124105f0-c5da-4498-b5d7-80f47bafa776
-- title:
--   Sum of integers below 360
-- statement:
--   The sum of the nonnegative integers strictly less than $360$ equals $64620$. Equivalently, $\\sum_{k=0}^{360-1} k = 360(360-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_360 : ∑ k ∈ range 360, k = 64620 := by sorry

end FiniteTriangular
