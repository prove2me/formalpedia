-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_908
-- name    : FiniteTriangular.sum_range_908
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:11.525651+00:00
-- url     : https://prove2.me/theorems/a54be4d0-a862-455f-a546-d198aa91e99a
-- title:
--   Sum of integers below 908
-- statement:
--   The sum of the nonnegative integers strictly less than $908$ equals $411778$. Equivalently, $\\sum_{k=0}^{908-1} k = 908(908-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_908 : ∑ k ∈ range 908, k = 411778 := by sorry

end FiniteTriangular
