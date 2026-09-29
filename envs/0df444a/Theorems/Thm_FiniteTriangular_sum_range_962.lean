-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_962
-- name    : FiniteTriangular.sum_range_962
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:36.438173+00:00
-- url     : https://prove2.me/theorems/b55e673d-3273-4254-9f5a-ff46a6ded84e
-- title:
--   Sum of integers below 962
-- statement:
--   The sum of the nonnegative integers strictly less than $962$ equals $462241$. Equivalently, $\\sum_{k=0}^{962-1} k = 962(962-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_962 : ∑ k ∈ range 962, k = 462241 := by sorry

end FiniteTriangular
