-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_406
-- name    : FiniteTriangular.sum_range_406
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:25.039822+00:00
-- url     : https://prove2.me/theorems/a5658633-f489-40f5-89fd-0c37351cc39a
-- title:
--   Sum of integers below 406
-- statement:
--   The sum of the nonnegative integers strictly less than $406$ equals $82215$. Equivalently, $\\sum_{k=0}^{406-1} k = 406(406-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_406 : ∑ k ∈ range 406, k = 82215 := by sorry

end FiniteTriangular
