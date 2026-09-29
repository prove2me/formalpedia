-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_314
-- name    : FiniteTriangular.sum_range_314
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:22.50697+00:00
-- url     : https://prove2.me/theorems/4792b18e-4958-4a98-8458-5bd68cbc17aa
-- title:
--   Sum of integers below 314
-- statement:
--   The sum of the nonnegative integers strictly less than $314$ equals $49141$. Equivalently, $\\sum_{k=0}^{314-1} k = 314(314-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_314 : ∑ k ∈ range 314, k = 49141 := by sorry

end FiniteTriangular
