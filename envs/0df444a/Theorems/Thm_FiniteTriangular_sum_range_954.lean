-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_954
-- name    : FiniteTriangular.sum_range_954
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:49.20048+00:00
-- url     : https://prove2.me/theorems/0d11de37-7072-494e-8a53-879594c863c9
-- title:
--   Sum of integers below 954
-- statement:
--   The sum of the nonnegative integers strictly less than $954$ equals $454581$. Equivalently, $\\sum_{k=0}^{954-1} k = 954(954-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_954 : ∑ k ∈ range 954, k = 454581 := by sorry

end FiniteTriangular
