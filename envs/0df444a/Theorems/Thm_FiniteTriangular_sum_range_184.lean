-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_184
-- name    : FiniteTriangular.sum_range_184
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:01.481466+00:00
-- url     : https://prove2.me/theorems/b7f42e6d-8160-4f11-855f-6f5c97f433d1
-- title:
--   Sum of integers below 184
-- statement:
--   The sum of the nonnegative integers strictly less than $184$ equals $16836$. Equivalently, $\sum_{k=0}^{184-1} k = 184(184-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_184 : ∑ k ∈ range 184, k = 16836 := by sorry

end FiniteTriangular
