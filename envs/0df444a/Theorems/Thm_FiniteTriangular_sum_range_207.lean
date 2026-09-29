-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_207
-- name    : FiniteTriangular.sum_range_207
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:18.109562+00:00
-- url     : https://prove2.me/theorems/7fc0206c-91cf-4ab2-aaac-0645a59cd3a9
-- title:
--   Sum of integers below 207
-- statement:
--   The sum of the nonnegative integers strictly less than $207$ equals $21321$. Equivalently, $\\sum_{k=0}^{207-1} k = 207(207-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_207 : ∑ k ∈ range 207, k = 21321 := by sorry

end FiniteTriangular
