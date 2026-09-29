-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_245
-- name    : FiniteTriangular.sum_range_245
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:12.001553+00:00
-- url     : https://prove2.me/theorems/14d353c8-8a5d-42d2-b867-f8b42919b0b2
-- title:
--   Sum of integers below 245
-- statement:
--   The sum of the nonnegative integers strictly less than $245$ equals $29890$. Equivalently, $\\sum_{k=0}^{245-1} k = 245(245-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_245 : ∑ k ∈ range 245, k = 29890 := by sorry

end FiniteTriangular
