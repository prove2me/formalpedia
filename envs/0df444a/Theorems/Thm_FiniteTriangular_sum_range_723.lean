-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_723
-- name    : FiniteTriangular.sum_range_723
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:50.813948+00:00
-- url     : https://prove2.me/theorems/8d425153-3be2-4954-b18e-cb8978800cf0
-- title:
--   Sum of integers below 723
-- statement:
--   The sum of the nonnegative integers strictly less than $723$ equals $261003$. Equivalently, $\\sum_{k=0}^{723-1} k = 723(723-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_723 : ∑ k ∈ range 723, k = 261003 := by sorry

end FiniteTriangular
