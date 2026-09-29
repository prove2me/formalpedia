-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_30
-- name    : FiniteTriangular.sum_range_30
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:08.17107+00:00
-- url     : https://prove2.me/theorems/407326f8-8537-49fd-802c-64229bbe5d86
-- title:
--   Sum of integers below 30
-- statement:
--   The sum of the nonnegative integers strictly less than $30$ equals $435$. Equivalently, $\sum_{k=0}^{30-1} k = 30(30-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_30 : ∑ k ∈ range 30, k = 435 := by sorry

end FiniteTriangular
