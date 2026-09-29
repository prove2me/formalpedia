-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_156
-- name    : FiniteTriangular.sum_range_156
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:20.037297+00:00
-- url     : https://prove2.me/theorems/a99db396-0698-44ca-96b3-ba943b649352
-- title:
--   Sum of integers below 156
-- statement:
--   The sum of the nonnegative integers strictly less than $156$ equals $12090$. Equivalently, $\sum_{k=0}^{156-1} k = 156(156-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_156 : ∑ k ∈ range 156, k = 12090 := by sorry

end FiniteTriangular
