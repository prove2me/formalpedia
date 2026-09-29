-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_252
-- name    : FiniteTriangular.sum_range_252
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:04.055248+00:00
-- url     : https://prove2.me/theorems/6396a237-1ba8-4687-ba51-f757fb6d12a8
-- title:
--   Sum of integers below 252
-- statement:
--   The sum of the nonnegative integers strictly less than $252$ equals $31626$. Equivalently, $\\sum_{k=0}^{252-1} k = 252(252-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_252 : ∑ k ∈ range 252, k = 31626 := by sorry

end FiniteTriangular
