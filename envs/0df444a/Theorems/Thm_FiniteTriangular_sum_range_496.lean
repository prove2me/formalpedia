-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_496
-- name    : FiniteTriangular.sum_range_496
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:46.435501+00:00
-- url     : https://prove2.me/theorems/c8b8d9ed-9580-475f-818b-7023e7b95ad1
-- title:
--   Sum of integers below 496
-- statement:
--   The sum of the nonnegative integers strictly less than $496$ equals $122760$. Equivalently, $\\sum_{k=0}^{496-1} k = 496(496-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_496 : ∑ k ∈ range 496, k = 122760 := by sorry

end FiniteTriangular
