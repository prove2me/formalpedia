-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_127
-- name    : FiniteTriangular.sum_range_127
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:08.368903+00:00
-- url     : https://prove2.me/theorems/3a27528e-fc72-4efa-ba1b-818e054e50a2
-- title:
--   Sum of integers below 127
-- statement:
--   The sum of the nonnegative integers strictly less than $127$ equals $8001$. Equivalently, $\sum_{k=0}^{127-1} k = 127(127-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_127 : ∑ k ∈ range 127, k = 8001 := by sorry

end FiniteTriangular
