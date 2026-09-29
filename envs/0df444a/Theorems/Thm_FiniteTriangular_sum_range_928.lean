-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_928
-- name    : FiniteTriangular.sum_range_928
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:33.415523+00:00
-- url     : https://prove2.me/theorems/7c0035c4-dd48-4c19-aeed-078bef8ab0a2
-- title:
--   Sum of integers below 928
-- statement:
--   The sum of the nonnegative integers strictly less than $928$ equals $430128$. Equivalently, $\\sum_{k=0}^{928-1} k = 928(928-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_928 : ∑ k ∈ range 928, k = 430128 := by sorry

end FiniteTriangular
