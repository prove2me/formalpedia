-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_940
-- name    : FiniteTriangular.sum_range_940
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:56:58.847033+00:00
-- url     : https://prove2.me/theorems/40ed2583-753b-4124-85b4-0daaff5b0398
-- title:
--   Sum of integers below 940
-- statement:
--   The sum of the nonnegative integers strictly less than $940$ equals $441330$. Equivalently, $\\sum_{k=0}^{940-1} k = 940(940-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_940 : ∑ k ∈ range 940, k = 441330 := by sorry

end FiniteTriangular
