-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_22
-- name    : FiniteTriangular.sum_range_22
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:08:09.191987+00:00
-- url     : https://prove2.me/theorems/6d2fcf25-eb16-4e11-89b6-95064985539d
-- title:
--   Sum of integers below 22
-- statement:
--   The sum of the nonnegative integers strictly less than $22$ equals $231$. Equivalently, $\sum_{k=0}^{22-1} k = 22(22-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_22 : ∑ k ∈ range 22, k = 231 := by sorry

end FiniteTriangular
