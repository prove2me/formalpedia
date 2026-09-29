-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_903
-- name    : FiniteTriangular.sum_range_903
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:33.406598+00:00
-- url     : https://prove2.me/theorems/2fa058fd-b195-4402-9ade-224bb0753b16
-- title:
--   Sum of integers below 903
-- statement:
--   The sum of the nonnegative integers strictly less than $903$ equals $407253$. Equivalently, $\\sum_{k=0}^{903-1} k = 903(903-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_903 : ∑ k ∈ range 903, k = 407253 := by sorry

end FiniteTriangular
