-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_189
-- name    : FiniteTriangular.sum_range_189
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:08.966299+00:00
-- url     : https://prove2.me/theorems/204af678-1f62-47e7-9945-af5c70fb6479
-- title:
--   Sum of integers below 189
-- statement:
--   The sum of the nonnegative integers strictly less than $189$ equals $17766$. Equivalently, $\\sum_{k=0}^{189-1} k = 189(189-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_189 : ∑ k ∈ range 189, k = 17766 := by sorry

end FiniteTriangular
