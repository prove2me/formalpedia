-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_262
-- name    : FiniteTriangular.sum_range_262
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:07.493962+00:00
-- url     : https://prove2.me/theorems/a6a84b0f-04c4-4151-bd6d-9b6ca50f3437
-- title:
--   Sum of integers below 262
-- statement:
--   The sum of the nonnegative integers strictly less than $262$ equals $34191$. Equivalently, $\\sum_{k=0}^{262-1} k = 262(262-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_262 : ∑ k ∈ range 262, k = 34191 := by sorry

end FiniteTriangular
