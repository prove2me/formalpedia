-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_396
-- name    : FiniteTriangular.sum_range_396
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:43.334067+00:00
-- url     : https://prove2.me/theorems/429e09ad-a6b7-45c6-9197-b27e5a153ca9
-- title:
--   Sum of integers below 396
-- statement:
--   The sum of the nonnegative integers strictly less than $396$ equals $78210$. Equivalently, $\\sum_{k=0}^{396-1} k = 396(396-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_396 : ∑ k ∈ range 396, k = 78210 := by sorry

end FiniteTriangular
