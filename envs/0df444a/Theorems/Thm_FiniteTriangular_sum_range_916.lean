-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_916
-- name    : FiniteTriangular.sum_range_916
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:47.014835+00:00
-- url     : https://prove2.me/theorems/c08cbb73-2cbf-4585-b3f7-92928583f7eb
-- title:
--   Sum of integers below 916
-- statement:
--   The sum of the nonnegative integers strictly less than $916$ equals $419070$. Equivalently, $\\sum_{k=0}^{916-1} k = 916(916-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_916 : ∑ k ∈ range 916, k = 419070 := by sorry

end FiniteTriangular
