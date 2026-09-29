-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_646
-- name    : FiniteTriangular.sum_range_646
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:15.767481+00:00
-- url     : https://prove2.me/theorems/21d44336-12b4-4f16-af51-bd5ccb1875c2
-- title:
--   Sum of integers below 646
-- statement:
--   The sum of the nonnegative integers strictly less than $646$ equals $208335$. Equivalently, $\\sum_{k=0}^{646-1} k = 646(646-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_646 : ∑ k ∈ range 646, k = 208335 := by sorry

end FiniteTriangular
