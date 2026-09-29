-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_480
-- name    : FiniteTriangular.sum_range_480
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:29.101569+00:00
-- url     : https://prove2.me/theorems/216fe0e5-63d6-4dfe-85da-a5fd1ff08ea8
-- title:
--   Sum of integers below 480
-- statement:
--   The sum of the nonnegative integers strictly less than $480$ equals $114960$. Equivalently, $\\sum_{k=0}^{480-1} k = 480(480-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_480 : ∑ k ∈ range 480, k = 114960 := by sorry

end FiniteTriangular
