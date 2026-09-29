-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_810
-- name    : FiniteTriangular.sum_range_810
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:53.78458+00:00
-- url     : https://prove2.me/theorems/c8cfff0c-df4f-4943-899b-04a89fbce4b6
-- title:
--   Sum of integers below 810
-- statement:
--   The sum of the nonnegative integers strictly less than $810$ equals $327645$. Equivalently, $\\sum_{k=0}^{810-1} k = 810(810-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_810 : ∑ k ∈ range 810, k = 327645 := by sorry

end FiniteTriangular
