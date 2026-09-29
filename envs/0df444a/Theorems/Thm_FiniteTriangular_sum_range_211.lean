-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_211
-- name    : FiniteTriangular.sum_range_211
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:32.111523+00:00
-- url     : https://prove2.me/theorems/18b0fb53-09fe-4435-b793-c67a0cf087d1
-- title:
--   Sum of integers below 211
-- statement:
--   The sum of the nonnegative integers strictly less than $211$ equals $22155$. Equivalently, $\\sum_{k=0}^{211-1} k = 211(211-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_211 : ∑ k ∈ range 211, k = 22155 := by sorry

end FiniteTriangular
