-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_219
-- name    : FiniteTriangular.sum_range_219
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:16.249726+00:00
-- url     : https://prove2.me/theorems/1f96a7b4-d4ea-45b4-b077-de9bd772eadc
-- title:
--   Sum of integers below 219
-- statement:
--   The sum of the nonnegative integers strictly less than $219$ equals $23871$. Equivalently, $\\sum_{k=0}^{219-1} k = 219(219-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_219 : ∑ k ∈ range 219, k = 23871 := by sorry

end FiniteTriangular
