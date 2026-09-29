-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_923
-- name    : FiniteTriangular.sum_range_923
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:36.393711+00:00
-- url     : https://prove2.me/theorems/f6821973-939d-439f-95ed-4031c93ddbe7
-- title:
--   Sum of integers below 923
-- statement:
--   The sum of the nonnegative integers strictly less than $923$ equals $425503$. Equivalently, $\\sum_{k=0}^{923-1} k = 923(923-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_923 : ∑ k ∈ range 923, k = 425503 := by sorry

end FiniteTriangular
