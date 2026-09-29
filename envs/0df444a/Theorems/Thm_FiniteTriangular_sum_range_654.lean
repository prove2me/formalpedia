-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_654
-- name    : FiniteTriangular.sum_range_654
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:52.528821+00:00
-- url     : https://prove2.me/theorems/81670a2f-d96d-4691-90b0-748b6f9e3917
-- title:
--   Sum of integers below 654
-- statement:
--   The sum of the nonnegative integers strictly less than $654$ equals $213531$. Equivalently, $\\sum_{k=0}^{654-1} k = 654(654-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_654 : ∑ k ∈ range 654, k = 213531 := by sorry

end FiniteTriangular
