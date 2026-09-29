-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_215
-- name    : FiniteTriangular.sum_range_215
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:33.49302+00:00
-- url     : https://prove2.me/theorems/7c7b10c7-6820-4f71-b760-506ae650b808
-- title:
--   Sum of integers below 215
-- statement:
--   The sum of the nonnegative integers strictly less than $215$ equals $23005$. Equivalently, $\\sum_{k=0}^{215-1} k = 215(215-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_215 : ∑ k ∈ range 215, k = 23005 := by sorry

end FiniteTriangular
