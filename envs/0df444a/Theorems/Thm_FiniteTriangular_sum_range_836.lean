-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_836
-- name    : FiniteTriangular.sum_range_836
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:10.283718+00:00
-- url     : https://prove2.me/theorems/dcfb57cd-17ba-4cc6-a129-90c5acfdcf7d
-- title:
--   Sum of integers below 836
-- statement:
--   The sum of the nonnegative integers strictly less than $836$ equals $349030$. Equivalently, $\\sum_{k=0}^{836-1} k = 836(836-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_836 : ∑ k ∈ range 836, k = 349030 := by sorry

end FiniteTriangular
