-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_471
-- name    : FiniteTriangular.sum_range_471
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:39.240639+00:00
-- url     : https://prove2.me/theorems/9bc57386-f430-46a4-94b7-176f249ea524
-- title:
--   Sum of integers below 471
-- statement:
--   The sum of the nonnegative integers strictly less than $471$ equals $110685$. Equivalently, $\\sum_{k=0}^{471-1} k = 471(471-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_471 : ∑ k ∈ range 471, k = 110685 := by sorry

end FiniteTriangular
