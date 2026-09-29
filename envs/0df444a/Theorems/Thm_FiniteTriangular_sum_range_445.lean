-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_445
-- name    : FiniteTriangular.sum_range_445
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:03.434986+00:00
-- url     : https://prove2.me/theorems/f13158b2-c0ab-4fce-a56c-753bfd65b003
-- title:
--   Sum of integers below 445
-- statement:
--   The sum of the nonnegative integers strictly less than $445$ equals $98790$. Equivalently, $\\sum_{k=0}^{445-1} k = 445(445-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_445 : ∑ k ∈ range 445, k = 98790 := by sorry

end FiniteTriangular
