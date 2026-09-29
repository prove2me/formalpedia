-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_969
-- name    : FiniteTriangular.sum_range_969
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:13.742289+00:00
-- url     : https://prove2.me/theorems/86a50ec8-b0d6-404c-9fec-7ac3b4c2e615
-- title:
--   Sum of integers below 969
-- statement:
--   The sum of the nonnegative integers strictly less than $969$ equals $468996$. Equivalently, $\\sum_{k=0}^{969-1} k = 969(969-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_969 : ∑ k ∈ range 969, k = 468996 := by sorry

end FiniteTriangular
