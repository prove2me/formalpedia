-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_267
-- name    : FiniteTriangular.sum_range_267
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:50.661183+00:00
-- url     : https://prove2.me/theorems/8138778f-8b15-43fd-9336-232ab3280ed5
-- title:
--   Sum of integers below 267
-- statement:
--   The sum of the nonnegative integers strictly less than $267$ equals $35511$. Equivalently, $\\sum_{k=0}^{267-1} k = 267(267-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_267 : ∑ k ∈ range 267, k = 35511 := by sorry

end FiniteTriangular
