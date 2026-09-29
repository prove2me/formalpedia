-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_662
-- name    : FiniteTriangular.sum_range_662
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:37.804522+00:00
-- url     : https://prove2.me/theorems/dfddd49a-b12a-48fb-b3ee-ade816e54355
-- title:
--   Sum of integers below 662
-- statement:
--   The sum of the nonnegative integers strictly less than $662$ equals $218791$. Equivalently, $\\sum_{k=0}^{662-1} k = 662(662-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_662 : ∑ k ∈ range 662, k = 218791 := by sorry

end FiniteTriangular
