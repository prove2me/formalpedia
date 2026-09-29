-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_580
-- name    : FiniteTriangular.sum_range_580
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:36.360677+00:00
-- url     : https://prove2.me/theorems/e5a0630b-e1b9-410b-8ae6-51b365962dca
-- title:
--   Sum of integers below 580
-- statement:
--   The sum of the nonnegative integers strictly less than $580$ equals $167910$. Equivalently, $\\sum_{k=0}^{580-1} k = 580(580-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_580 : ∑ k ∈ range 580, k = 167910 := by sorry

end FiniteTriangular
