-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_19
-- name    : FiniteTriangular.sum_range_19
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:07:37.107369+00:00
-- url     : https://prove2.me/theorems/df84db74-a069-4348-89e2-c5e789c9e89d
-- title:
--   Sum of integers below 19
-- statement:
--   The sum of the nonnegative integers strictly less than $19$ equals $171$. Equivalently, $\sum_{k=0}^{19-1} k = 19(19-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_19 : ∑ k ∈ range 19, k = 171 := by sorry

end FiniteTriangular
