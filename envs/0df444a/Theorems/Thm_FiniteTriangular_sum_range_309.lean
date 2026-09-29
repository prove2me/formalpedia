-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_309
-- name    : FiniteTriangular.sum_range_309
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:55.736196+00:00
-- url     : https://prove2.me/theorems/6b93e8d0-5869-4a60-8843-d4dd7d29ce2f
-- title:
--   Sum of integers below 309
-- statement:
--   The sum of the nonnegative integers strictly less than $309$ equals $47586$. Equivalently, $\\sum_{k=0}^{309-1} k = 309(309-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_309 : ∑ k ∈ range 309, k = 47586 := by sorry

end FiniteTriangular
