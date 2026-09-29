-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_131
-- name    : FiniteTriangular.sum_range_131
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:50.858108+00:00
-- url     : https://prove2.me/theorems/120b2423-8b14-4eec-bfc3-f47dec7f894a
-- title:
--   Sum of integers below 131
-- statement:
--   The sum of the nonnegative integers strictly less than $131$ equals $8515$. Equivalently, $\sum_{k=0}^{131-1} k = 131(131-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_131 : ∑ k ∈ range 131, k = 8515 := by sorry

end FiniteTriangular
