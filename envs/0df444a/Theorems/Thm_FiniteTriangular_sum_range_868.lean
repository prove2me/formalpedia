-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_868
-- name    : FiniteTriangular.sum_range_868
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:47.221992+00:00
-- url     : https://prove2.me/theorems/4de64126-6e9b-457f-8016-c85e2fa52e53
-- title:
--   Sum of integers below 868
-- statement:
--   The sum of the nonnegative integers strictly less than $868$ equals $376278$. Equivalently, $\\sum_{k=0}^{868-1} k = 868(868-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_868 : ∑ k ∈ range 868, k = 376278 := by sorry

end FiniteTriangular
