-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_665
-- name    : FiniteTriangular.sum_range_665
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:11.059922+00:00
-- url     : https://prove2.me/theorems/c13c0914-ebc4-407d-ae91-3883b7f8859e
-- title:
--   Sum of integers below 665
-- statement:
--   The sum of the nonnegative integers strictly less than $665$ equals $220780$. Equivalently, $\\sum_{k=0}^{665-1} k = 665(665-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_665 : ∑ k ∈ range 665, k = 220780 := by sorry

end FiniteTriangular
