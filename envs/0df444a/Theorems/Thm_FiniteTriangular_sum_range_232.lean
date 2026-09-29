-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_232
-- name    : FiniteTriangular.sum_range_232
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:01.835601+00:00
-- url     : https://prove2.me/theorems/3f9b3e77-a2c8-45d6-9e0d-f49f245dd3dc
-- title:
--   Sum of integers below 232
-- statement:
--   The sum of the nonnegative integers strictly less than $232$ equals $26796$. Equivalently, $\\sum_{k=0}^{232-1} k = 232(232-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_232 : ∑ k ∈ range 232, k = 26796 := by sorry

end FiniteTriangular
