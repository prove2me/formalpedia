-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_965
-- name    : FiniteTriangular.sum_range_965
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:36.972353+00:00
-- url     : https://prove2.me/theorems/dc346f9f-1d38-4a0d-9d26-082214ff47bf
-- title:
--   Sum of integers below 965
-- statement:
--   The sum of the nonnegative integers strictly less than $965$ equals $465130$. Equivalently, $\\sum_{k=0}^{965-1} k = 965(965-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_965 : ∑ k ∈ range 965, k = 465130 := by sorry

end FiniteTriangular
