-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_286
-- name    : FiniteTriangular.sum_range_286
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:29.961834+00:00
-- url     : https://prove2.me/theorems/6cb70541-fd8a-48a3-8d3a-4bc2ca801683
-- title:
--   Sum of integers below 286
-- statement:
--   The sum of the nonnegative integers strictly less than $286$ equals $40755$. Equivalently, $\\sum_{k=0}^{286-1} k = 286(286-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_286 : ∑ k ∈ range 286, k = 40755 := by sorry

end FiniteTriangular
