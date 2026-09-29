-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_564
-- name    : FiniteTriangular.sum_range_564
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:06.47658+00:00
-- url     : https://prove2.me/theorems/b3755cce-1342-4546-b9af-b8cfc21e6a94
-- title:
--   Sum of integers below 564
-- statement:
--   The sum of the nonnegative integers strictly less than $564$ equals $158766$. Equivalently, $\\sum_{k=0}^{564-1} k = 564(564-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_564 : ∑ k ∈ range 564, k = 158766 := by sorry

end FiniteTriangular
