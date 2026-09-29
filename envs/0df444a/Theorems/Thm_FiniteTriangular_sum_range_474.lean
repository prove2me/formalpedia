-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_474
-- name    : FiniteTriangular.sum_range_474
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:29.948213+00:00
-- url     : https://prove2.me/theorems/126e564b-eb0c-49a3-b0dd-ad1530a0de5e
-- title:
--   Sum of integers below 474
-- statement:
--   The sum of the nonnegative integers strictly less than $474$ equals $112101$. Equivalently, $\\sum_{k=0}^{474-1} k = 474(474-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_474 : ∑ k ∈ range 474, k = 112101 := by sorry

end FiniteTriangular
