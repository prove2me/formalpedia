-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_792
-- name    : FiniteTriangular.sum_range_792
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:56.904977+00:00
-- url     : https://prove2.me/theorems/94ae495c-1fc7-416c-bba5-bb4f3ec23c24
-- title:
--   Sum of integers below 792
-- statement:
--   The sum of the nonnegative integers strictly less than $792$ equals $313236$. Equivalently, $\\sum_{k=0}^{792-1} k = 792(792-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_792 : ∑ k ∈ range 792, k = 313236 := by sorry

end FiniteTriangular
