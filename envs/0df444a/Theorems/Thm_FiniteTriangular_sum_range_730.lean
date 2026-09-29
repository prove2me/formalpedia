-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_730
-- name    : FiniteTriangular.sum_range_730
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:31.176449+00:00
-- url     : https://prove2.me/theorems/05f066cf-a5fa-4db2-aa95-4a738f02e3ad
-- title:
--   Sum of integers below 730
-- statement:
--   The sum of the nonnegative integers strictly less than $730$ equals $266085$. Equivalently, $\\sum_{k=0}^{730-1} k = 730(730-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_730 : ∑ k ∈ range 730, k = 266085 := by sorry

end FiniteTriangular
