-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_194
-- name    : FiniteTriangular.sum_range_194
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:22.237871+00:00
-- url     : https://prove2.me/theorems/b2b09fcf-8328-4ef0-afd0-6fbcda7c6135
-- title:
--   Sum of integers below 194
-- statement:
--   The sum of the nonnegative integers strictly less than $194$ equals $18721$. Equivalently, $\\sum_{k=0}^{194-1} k = 194(194-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_194 : ∑ k ∈ range 194, k = 18721 := by sorry

end FiniteTriangular
