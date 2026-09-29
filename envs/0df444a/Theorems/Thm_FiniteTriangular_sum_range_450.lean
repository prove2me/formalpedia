-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_450
-- name    : FiniteTriangular.sum_range_450
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:48.407409+00:00
-- url     : https://prove2.me/theorems/84f3ae69-ba69-4b47-a5e6-cd97bffc3bc0
-- title:
--   Sum of integers below 450
-- statement:
--   The sum of the nonnegative integers strictly less than $450$ equals $101025$. Equivalently, $\\sum_{k=0}^{450-1} k = 450(450-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_450 : ∑ k ∈ range 450, k = 101025 := by sorry

end FiniteTriangular
