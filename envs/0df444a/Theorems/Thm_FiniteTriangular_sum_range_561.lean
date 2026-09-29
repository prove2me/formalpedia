-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_561
-- name    : FiniteTriangular.sum_range_561
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:07.640422+00:00
-- url     : https://prove2.me/theorems/484a4a15-c78d-4d10-97a0-eb7794962941
-- title:
--   Sum of integers below 561
-- statement:
--   The sum of the nonnegative integers strictly less than $561$ equals $157080$. Equivalently, $\\sum_{k=0}^{561-1} k = 561(561-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_561 : ∑ k ∈ range 561, k = 157080 := by sorry

end FiniteTriangular
