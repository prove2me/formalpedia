-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_671
-- name    : FiniteTriangular.sum_range_671
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:12.038222+00:00
-- url     : https://prove2.me/theorems/60d4df7f-47eb-43c5-a4da-f4f42a48c1f7
-- title:
--   Sum of integers below 671
-- statement:
--   The sum of the nonnegative integers strictly less than $671$ equals $224785$. Equivalently, $\\sum_{k=0}^{671-1} k = 671(671-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_671 : ∑ k ∈ range 671, k = 224785 := by sorry

end FiniteTriangular
