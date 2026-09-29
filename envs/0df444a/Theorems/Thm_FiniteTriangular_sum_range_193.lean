-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_193
-- name    : FiniteTriangular.sum_range_193
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:24.343807+00:00
-- url     : https://prove2.me/theorems/f94b8522-2a0d-48fd-a61d-6ef2ccb1d8ec
-- title:
--   Sum of integers below 193
-- statement:
--   The sum of the nonnegative integers strictly less than $193$ equals $18528$. Equivalently, $\\sum_{k=0}^{193-1} k = 193(193-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_193 : ∑ k ∈ range 193, k = 18528 := by sorry

end FiniteTriangular
