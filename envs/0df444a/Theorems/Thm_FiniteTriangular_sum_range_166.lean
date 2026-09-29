-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_166
-- name    : FiniteTriangular.sum_range_166
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:50.119967+00:00
-- url     : https://prove2.me/theorems/34cd3ec9-f1f3-4709-bf0d-ced6f54b3e8d
-- title:
--   Sum of integers below 166
-- statement:
--   The sum of the nonnegative integers strictly less than $166$ equals $13695$. Equivalently, $\sum_{k=0}^{166-1} k = 166(166-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_166 : ∑ k ∈ range 166, k = 13695 := by sorry

end FiniteTriangular
