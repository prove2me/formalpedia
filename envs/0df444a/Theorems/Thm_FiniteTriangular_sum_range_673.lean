-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_673
-- name    : FiniteTriangular.sum_range_673
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:55.885694+00:00
-- url     : https://prove2.me/theorems/1190b56d-347c-4499-bb2f-5ab4dc5516d5
-- title:
--   Sum of integers below 673
-- statement:
--   The sum of the nonnegative integers strictly less than $673$ equals $226128$. Equivalently, $\\sum_{k=0}^{673-1} k = 673(673-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_673 : ∑ k ∈ range 673, k = 226128 := by sorry

end FiniteTriangular
