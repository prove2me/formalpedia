-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_340
-- name    : FiniteTriangular.sum_range_340
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:52.154635+00:00
-- url     : https://prove2.me/theorems/ceb2759b-926d-4629-8474-b3438ffe1cec
-- title:
--   Sum of integers below 340
-- statement:
--   The sum of the nonnegative integers strictly less than $340$ equals $57630$. Equivalently, $\\sum_{k=0}^{340-1} k = 340(340-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_340 : ∑ k ∈ range 340, k = 57630 := by sorry

end FiniteTriangular
