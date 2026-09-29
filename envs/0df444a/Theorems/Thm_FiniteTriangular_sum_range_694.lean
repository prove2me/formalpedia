-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_694
-- name    : FiniteTriangular.sum_range_694
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:25.69699+00:00
-- url     : https://prove2.me/theorems/50c2935b-c9f4-4a8a-8196-619cd52668a2
-- title:
--   Sum of integers below 694
-- statement:
--   The sum of the nonnegative integers strictly less than $694$ equals $240471$. Equivalently, $\\sum_{k=0}^{694-1} k = 694(694-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_694 : ∑ k ∈ range 694, k = 240471 := by sorry

end FiniteTriangular
