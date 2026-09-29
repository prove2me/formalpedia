-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_13
-- name    : FiniteTriangular.sum_range_13
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:03:48.938141+00:00
-- url     : https://prove2.me/theorems/1cfa0151-d852-4668-8090-08818ae257bf
-- title:
--   Sum of integers below 13
-- statement:
--   The sum of the nonnegative integers strictly less than $13$ equals $78$. Equivalently, $\sum_{k=0}^{13-1} k = 13(13-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_13 : ∑ k ∈ range 13, k = 78 := by sorry

end FiniteTriangular
