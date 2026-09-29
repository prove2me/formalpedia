-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_137
-- name    : FiniteTriangular.sum_range_137
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:02.158499+00:00
-- url     : https://prove2.me/theorems/f63f6d83-aa96-4397-8835-4bb714eac86b
-- title:
--   Sum of integers below 137
-- statement:
--   The sum of the nonnegative integers strictly less than $137$ equals $9316$. Equivalently, $\sum_{k=0}^{137-1} k = 137(137-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_137 : ∑ k ∈ range 137, k = 9316 := by sorry

end FiniteTriangular
