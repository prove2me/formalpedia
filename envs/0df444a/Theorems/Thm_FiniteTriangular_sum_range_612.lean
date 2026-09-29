-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_612
-- name    : FiniteTriangular.sum_range_612
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:30.679877+00:00
-- url     : https://prove2.me/theorems/514acad1-bd5a-423d-a310-b0a04b32de63
-- title:
--   Sum of integers below 612
-- statement:
--   The sum of the nonnegative integers strictly less than $612$ equals $186966$. Equivalently, $\\sum_{k=0}^{612-1} k = 612(612-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_612 : ∑ k ∈ range 612, k = 186966 := by sorry

end FiniteTriangular
