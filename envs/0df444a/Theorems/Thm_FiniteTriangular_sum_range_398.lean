-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_398
-- name    : FiniteTriangular.sum_range_398
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:45.863323+00:00
-- url     : https://prove2.me/theorems/7fdf62be-a956-47f0-82ad-6b8ab59956b0
-- title:
--   Sum of integers below 398
-- statement:
--   The sum of the nonnegative integers strictly less than $398$ equals $79003$. Equivalently, $\\sum_{k=0}^{398-1} k = 398(398-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_398 : ∑ k ∈ range 398, k = 79003 := by sorry

end FiniteTriangular
