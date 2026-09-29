-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_931
-- name    : FiniteTriangular.sum_range_931
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:12.217981+00:00
-- url     : https://prove2.me/theorems/2dbfd749-62c6-4304-a917-992b800eb8f4
-- title:
--   Sum of integers below 931
-- statement:
--   The sum of the nonnegative integers strictly less than $931$ equals $432915$. Equivalently, $\\sum_{k=0}^{931-1} k = 931(931-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_931 : ∑ k ∈ range 931, k = 432915 := by sorry

end FiniteTriangular
