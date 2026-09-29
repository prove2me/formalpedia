-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_608
-- name    : FiniteTriangular.sum_range_608
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:43.24709+00:00
-- url     : https://prove2.me/theorems/6b22be44-9135-4f10-9f93-d585c60522fb
-- title:
--   Sum of integers below 608
-- statement:
--   The sum of the nonnegative integers strictly less than $608$ equals $184528$. Equivalently, $\\sum_{k=0}^{608-1} k = 608(608-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_608 : ∑ k ∈ range 608, k = 184528 := by sorry

end FiniteTriangular
