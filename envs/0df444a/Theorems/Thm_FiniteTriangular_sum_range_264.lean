-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_264
-- name    : FiniteTriangular.sum_range_264
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:06.531655+00:00
-- url     : https://prove2.me/theorems/fa8a26ea-c9f5-4bb5-b06d-a2588c34fd0f
-- title:
--   Sum of integers below 264
-- statement:
--   The sum of the nonnegative integers strictly less than $264$ equals $34716$. Equivalently, $\\sum_{k=0}^{264-1} k = 264(264-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_264 : ∑ k ∈ range 264, k = 34716 := by sorry

end FiniteTriangular
