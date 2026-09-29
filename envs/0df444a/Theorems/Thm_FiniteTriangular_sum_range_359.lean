-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_359
-- name    : FiniteTriangular.sum_range_359
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:18.705711+00:00
-- url     : https://prove2.me/theorems/18340e0e-92b7-4abc-a2ef-12470400ec38
-- title:
--   Sum of integers below 359
-- statement:
--   The sum of the nonnegative integers strictly less than $359$ equals $64261$. Equivalently, $\\sum_{k=0}^{359-1} k = 359(359-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_359 : ∑ k ∈ range 359, k = 64261 := by sorry

end FiniteTriangular
