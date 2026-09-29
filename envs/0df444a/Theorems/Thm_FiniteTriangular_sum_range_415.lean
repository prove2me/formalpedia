-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_415
-- name    : FiniteTriangular.sum_range_415
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:08.756659+00:00
-- url     : https://prove2.me/theorems/c8b2037f-ce1b-4409-9b05-488c6909f733
-- title:
--   Sum of integers below 415
-- statement:
--   The sum of the nonnegative integers strictly less than $415$ equals $85905$. Equivalently, $\\sum_{k=0}^{415-1} k = 415(415-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_415 : ∑ k ∈ range 415, k = 85905 := by sorry

end FiniteTriangular
