-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_31
-- name    : FiniteTriangular.sum_range_31
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:03.351987+00:00
-- url     : https://prove2.me/theorems/3a0b8e94-64b1-4d00-995e-b3745051edd0
-- title:
--   Sum of integers below 31
-- statement:
--   The sum of the nonnegative integers strictly less than $31$ equals $465$. Equivalently, $\sum_{k=0}^{31-1} k = 31(31-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_31 : ∑ k ∈ range 31, k = 465 := by sorry

end FiniteTriangular
