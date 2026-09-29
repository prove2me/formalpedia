-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_883
-- name    : FiniteTriangular.sum_range_883
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:08.001591+00:00
-- url     : https://prove2.me/theorems/b123b835-fb10-4f97-963d-a0b0e0cbc217
-- title:
--   Sum of integers below 883
-- statement:
--   The sum of the nonnegative integers strictly less than $883$ equals $389403$. Equivalently, $\\sum_{k=0}^{883-1} k = 883(883-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_883 : ∑ k ∈ range 883, k = 389403 := by sorry

end FiniteTriangular
