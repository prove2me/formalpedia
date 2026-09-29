-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_800
-- name    : FiniteTriangular.sum_range_800
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:33.479519+00:00
-- url     : https://prove2.me/theorems/f2c01a2f-b995-4d69-b9d0-fe971b8172df
-- title:
--   Sum of integers below 800
-- statement:
--   The sum of the nonnegative integers strictly less than $800$ equals $319600$. Equivalently, $\\sum_{k=0}^{800-1} k = 800(800-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_800 : ∑ k ∈ range 800, k = 319600 := by sorry

end FiniteTriangular
