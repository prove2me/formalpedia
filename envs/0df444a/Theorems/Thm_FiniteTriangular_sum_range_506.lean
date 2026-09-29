-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_506
-- name    : FiniteTriangular.sum_range_506
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:12.364504+00:00
-- url     : https://prove2.me/theorems/e77aeeb1-060a-4c45-9be9-aa9265b60995
-- title:
--   Sum of integers below 506
-- statement:
--   The sum of the nonnegative integers strictly less than $506$ equals $127765$. Equivalently, $\\sum_{k=0}^{506-1} k = 506(506-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_506 : ∑ k ∈ range 506, k = 127765 := by sorry

end FiniteTriangular
