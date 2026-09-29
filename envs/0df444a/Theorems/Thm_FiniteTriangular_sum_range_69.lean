-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_69
-- name    : FiniteTriangular.sum_range_69
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:55.787086+00:00
-- url     : https://prove2.me/theorems/7b9abc6f-e992-4213-a109-548833bf6727
-- title:
--   Sum of integers below 69
-- statement:
--   The sum of the nonnegative integers strictly less than $69$ equals $2346$. Equivalently, $\sum_{k=0}^{69-1} k = 69(69-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_69 : ∑ k ∈ range 69, k = 2346 := by sorry

end FiniteTriangular
