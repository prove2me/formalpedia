-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_749
-- name    : FiniteTriangular.sum_range_749
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:20.221799+00:00
-- url     : https://prove2.me/theorems/7c068956-6dbc-4a1f-9605-2d8c47c8eda0
-- title:
--   Sum of integers below 749
-- statement:
--   The sum of the nonnegative integers strictly less than $749$ equals $280126$. Equivalently, $\\sum_{k=0}^{749-1} k = 749(749-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_749 : ∑ k ∈ range 749, k = 280126 := by sorry

end FiniteTriangular
