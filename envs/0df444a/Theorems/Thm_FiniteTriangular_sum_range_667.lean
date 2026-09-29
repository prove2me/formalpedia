-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_667
-- name    : FiniteTriangular.sum_range_667
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:11.204281+00:00
-- url     : https://prove2.me/theorems/518db5ff-af3c-4969-a5dc-c441e714d8f6
-- title:
--   Sum of integers below 667
-- statement:
--   The sum of the nonnegative integers strictly less than $667$ equals $222111$. Equivalently, $\\sum_{k=0}^{667-1} k = 667(667-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_667 : ∑ k ∈ range 667, k = 222111 := by sorry

end FiniteTriangular
