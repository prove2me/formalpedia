-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_875
-- name    : FiniteTriangular.sum_range_875
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:29.864621+00:00
-- url     : https://prove2.me/theorems/025f8638-bb2e-45d7-87c1-fb3080fa9414
-- title:
--   Sum of integers below 875
-- statement:
--   The sum of the nonnegative integers strictly less than $875$ equals $382375$. Equivalently, $\\sum_{k=0}^{875-1} k = 875(875-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_875 : ∑ k ∈ range 875, k = 382375 := by sorry

end FiniteTriangular
