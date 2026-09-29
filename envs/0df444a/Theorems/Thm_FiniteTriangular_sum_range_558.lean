-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_558
-- name    : FiniteTriangular.sum_range_558
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:15.716321+00:00
-- url     : https://prove2.me/theorems/531e37a9-b394-4517-8130-e46c1180c463
-- title:
--   Sum of integers below 558
-- statement:
--   The sum of the nonnegative integers strictly less than $558$ equals $155403$. Equivalently, $\\sum_{k=0}^{558-1} k = 558(558-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_558 : ∑ k ∈ range 558, k = 155403 := by sorry

end FiniteTriangular
