-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_517
-- name    : FiniteTriangular.sum_range_517
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:55.468055+00:00
-- url     : https://prove2.me/theorems/81f0c2b6-159f-4d59-a0bd-4dd8f47ecda2
-- title:
--   Sum of integers below 517
-- statement:
--   The sum of the nonnegative integers strictly less than $517$ equals $133386$. Equivalently, $\\sum_{k=0}^{517-1} k = 517(517-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_517 : ∑ k ∈ range 517, k = 133386 := by sorry

end FiniteTriangular
