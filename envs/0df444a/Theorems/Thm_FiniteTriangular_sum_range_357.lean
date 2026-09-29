-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_357
-- name    : FiniteTriangular.sum_range_357
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:18.123083+00:00
-- url     : https://prove2.me/theorems/3d1e3502-bca1-44c0-8193-0e6ec33770c6
-- title:
--   Sum of integers below 357
-- statement:
--   The sum of the nonnegative integers strictly less than $357$ equals $63546$. Equivalently, $\\sum_{k=0}^{357-1} k = 357(357-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_357 : ∑ k ∈ range 357, k = 63546 := by sorry

end FiniteTriangular
