-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_828
-- name    : FiniteTriangular.sum_range_828
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:30.077431+00:00
-- url     : https://prove2.me/theorems/a7321792-e072-47b3-8496-94a3175e0de5
-- title:
--   Sum of integers below 828
-- statement:
--   The sum of the nonnegative integers strictly less than $828$ equals $342378$. Equivalently, $\\sum_{k=0}^{828-1} k = 828(828-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_828 : ∑ k ∈ range 828, k = 342378 := by sorry

end FiniteTriangular
