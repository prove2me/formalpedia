-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_826
-- name    : FiniteTriangular.sum_range_826
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:29.139602+00:00
-- url     : https://prove2.me/theorems/b1fe89d0-aea3-4b4d-9e12-b17df466cda1
-- title:
--   Sum of integers below 826
-- statement:
--   The sum of the nonnegative integers strictly less than $826$ equals $340725$. Equivalently, $\\sum_{k=0}^{826-1} k = 826(826-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_826 : ∑ k ∈ range 826, k = 340725 := by sorry

end FiniteTriangular
