-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_697
-- name    : FiniteTriangular.sum_range_697
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:59.433557+00:00
-- url     : https://prove2.me/theorems/59d0ac02-61cf-4698-9532-f46b00e8008a
-- title:
--   Sum of integers below 697
-- statement:
--   The sum of the nonnegative integers strictly less than $697$ equals $242556$. Equivalently, $\\sum_{k=0}^{697-1} k = 697(697-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_697 : ∑ k ∈ range 697, k = 242556 := by sorry

end FiniteTriangular
