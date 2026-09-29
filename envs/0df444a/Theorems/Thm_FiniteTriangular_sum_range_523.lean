-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_523
-- name    : FiniteTriangular.sum_range_523
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:41.602421+00:00
-- url     : https://prove2.me/theorems/65bbfc06-df28-49f9-8722-b1185c3d9073
-- title:
--   Sum of integers below 523
-- statement:
--   The sum of the nonnegative integers strictly less than $523$ equals $136503$. Equivalently, $\\sum_{k=0}^{523-1} k = 523(523-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_523 : ∑ k ∈ range 523, k = 136503 := by sorry

end FiniteTriangular
