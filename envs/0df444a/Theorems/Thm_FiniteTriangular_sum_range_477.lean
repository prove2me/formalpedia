-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_477
-- name    : FiniteTriangular.sum_range_477
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:26.527349+00:00
-- url     : https://prove2.me/theorems/e510aa63-6f84-4002-b111-f7e580bf0b6d
-- title:
--   Sum of integers below 477
-- statement:
--   The sum of the nonnegative integers strictly less than $477$ equals $113526$. Equivalently, $\\sum_{k=0}^{477-1} k = 477(477-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_477 : ∑ k ∈ range 477, k = 113526 := by sorry

end FiniteTriangular
