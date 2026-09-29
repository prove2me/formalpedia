-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_555
-- name    : FiniteTriangular.sum_range_555
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:18.949606+00:00
-- url     : https://prove2.me/theorems/6df0f36a-be73-485b-858f-e52113a77053
-- title:
--   Sum of integers below 555
-- statement:
--   The sum of the nonnegative integers strictly less than $555$ equals $153735$. Equivalently, $\\sum_{k=0}^{555-1} k = 555(555-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_555 : ∑ k ∈ range 555, k = 153735 := by sorry

end FiniteTriangular
