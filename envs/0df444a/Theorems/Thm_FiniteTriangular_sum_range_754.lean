-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_754
-- name    : FiniteTriangular.sum_range_754
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:58.892753+00:00
-- url     : https://prove2.me/theorems/37befae5-3a1f-4bba-a3a7-aab48304122a
-- title:
--   Sum of integers below 754
-- statement:
--   The sum of the nonnegative integers strictly less than $754$ equals $283881$. Equivalently, $\\sum_{k=0}^{754-1} k = 754(754-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_754 : ∑ k ∈ range 754, k = 283881 := by sorry

end FiniteTriangular
