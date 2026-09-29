-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_465
-- name    : FiniteTriangular.sum_range_465
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:38.709773+00:00
-- url     : https://prove2.me/theorems/557b0339-8683-48d3-abc2-bc9c36a6fc56
-- title:
--   Sum of integers below 465
-- statement:
--   The sum of the nonnegative integers strictly less than $465$ equals $107880$. Equivalently, $\\sum_{k=0}^{465-1} k = 465(465-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_465 : ∑ k ∈ range 465, k = 107880 := by sorry

end FiniteTriangular
