-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_123
-- name    : FiniteTriangular.sum_range_123
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:04.925987+00:00
-- url     : https://prove2.me/theorems/159ee7b4-4feb-4299-814e-1fea60264e64
-- title:
--   Sum of integers below 123
-- statement:
--   The sum of the nonnegative integers strictly less than $123$ equals $7503$. Equivalently, $\sum_{k=0}^{123-1} k = 123(123-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_123 : ∑ k ∈ range 123, k = 7503 := by sorry

end FiniteTriangular
