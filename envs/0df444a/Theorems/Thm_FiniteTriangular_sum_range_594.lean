-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_594
-- name    : FiniteTriangular.sum_range_594
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:42:59.969083+00:00
-- url     : https://prove2.me/theorems/e9269c25-6d64-4bbe-9e2f-d37f7ea8ca14
-- title:
--   Sum of integers below 594
-- statement:
--   The sum of the nonnegative integers strictly less than $594$ equals $176121$. Equivalently, $\\sum_{k=0}^{594-1} k = 594(594-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_594 : ∑ k ∈ range 594, k = 176121 := by sorry

end FiniteTriangular
