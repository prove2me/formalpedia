-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_599
-- name    : FiniteTriangular.sum_range_599
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:42:57.168369+00:00
-- url     : https://prove2.me/theorems/d9ef4f49-3d43-45f2-bddf-80163f44723a
-- title:
--   Sum of integers below 599
-- statement:
--   The sum of the nonnegative integers strictly less than $599$ equals $179101$. Equivalently, $\\sum_{k=0}^{599-1} k = 599(599-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_599 : ∑ k ∈ range 599, k = 179101 := by sorry

end FiniteTriangular
