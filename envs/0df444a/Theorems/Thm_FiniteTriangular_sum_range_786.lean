-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_786
-- name    : FiniteTriangular.sum_range_786
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:54.010917+00:00
-- url     : https://prove2.me/theorems/8c32895e-b4b4-455b-92be-b734959f5712
-- title:
--   Sum of integers below 786
-- statement:
--   The sum of the nonnegative integers strictly less than $786$ equals $308505$. Equivalently, $\\sum_{k=0}^{786-1} k = 786(786-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_786 : ∑ k ∈ range 786, k = 308505 := by sorry

end FiniteTriangular
