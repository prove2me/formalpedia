-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_263
-- name    : FiniteTriangular.sum_range_263
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:01.838413+00:00
-- url     : https://prove2.me/theorems/4aa27ab9-b7b2-4b3b-aff5-c339fc00ba1b
-- title:
--   Sum of integers below 263
-- statement:
--   The sum of the nonnegative integers strictly less than $263$ equals $34453$. Equivalently, $\\sum_{k=0}^{263-1} k = 263(263-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_263 : ∑ k ∈ range 263, k = 34453 := by sorry

end FiniteTriangular
