-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_190
-- name    : FiniteTriangular.sum_range_190
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:08.323429+00:00
-- url     : https://prove2.me/theorems/b5a4a895-22b6-403e-a74d-4c1e7615faaf
-- title:
--   Sum of integers below 190
-- statement:
--   The sum of the nonnegative integers strictly less than $190$ equals $17955$. Equivalently, $\\sum_{k=0}^{190-1} k = 190(190-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_190 : ∑ k ∈ range 190, k = 17955 := by sorry

end FiniteTriangular
