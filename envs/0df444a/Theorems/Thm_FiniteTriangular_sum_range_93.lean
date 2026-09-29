-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_93
-- name    : FiniteTriangular.sum_range_93
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:45.942478+00:00
-- url     : https://prove2.me/theorems/24562109-5185-497c-acec-39dd40900ab9
-- title:
--   Sum of integers below 93
-- statement:
--   The sum of the nonnegative integers strictly less than $93$ equals $4278$. Equivalently, $\sum_{k=0}^{93-1} k = 93(93-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_93 : ∑ k ∈ range 93, k = 4278 := by sorry

end FiniteTriangular
