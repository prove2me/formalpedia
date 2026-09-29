-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_292
-- name    : FiniteTriangular.sum_range_292
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:05.488052+00:00
-- url     : https://prove2.me/theorems/5ace3c02-d475-449d-a496-fd92a623a4fd
-- title:
--   Sum of integers below 292
-- statement:
--   The sum of the nonnegative integers strictly less than $292$ equals $42486$. Equivalently, $\\sum_{k=0}^{292-1} k = 292(292-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_292 : ∑ k ∈ range 292, k = 42486 := by sorry

end FiniteTriangular
