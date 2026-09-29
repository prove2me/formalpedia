-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_769
-- name    : FiniteTriangular.sum_range_769
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:24.791332+00:00
-- url     : https://prove2.me/theorems/3d30d17b-3776-439c-a3cb-2c0c9dd9b5ab
-- title:
--   Sum of integers below 769
-- statement:
--   The sum of the nonnegative integers strictly less than $769$ equals $295296$. Equivalently, $\\sum_{k=0}^{769-1} k = 769(769-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_769 : ∑ k ∈ range 769, k = 295296 := by sorry

end FiniteTriangular
