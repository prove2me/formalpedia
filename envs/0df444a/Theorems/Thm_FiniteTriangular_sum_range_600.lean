-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_600
-- name    : FiniteTriangular.sum_range_600
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:42:57.512335+00:00
-- url     : https://prove2.me/theorems/951aeabb-ddd6-4425-8cc2-1c896ef71681
-- title:
--   Sum of integers below 600
-- statement:
--   The sum of the nonnegative integers strictly less than $600$ equals $179700$. Equivalently, $\\sum_{k=0}^{600-1} k = 600(600-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_600 : ∑ k ∈ range 600, k = 179700 := by sorry

end FiniteTriangular
