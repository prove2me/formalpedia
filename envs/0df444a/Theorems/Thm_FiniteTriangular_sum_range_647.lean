-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_647
-- name    : FiniteTriangular.sum_range_647
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:13.747007+00:00
-- url     : https://prove2.me/theorems/55561d03-0052-42f9-b1de-c5bb5634f2b0
-- title:
--   Sum of integers below 647
-- statement:
--   The sum of the nonnegative integers strictly less than $647$ equals $208981$. Equivalently, $\\sum_{k=0}^{647-1} k = 647(647-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_647 : ∑ k ∈ range 647, k = 208981 := by sorry

end FiniteTriangular
