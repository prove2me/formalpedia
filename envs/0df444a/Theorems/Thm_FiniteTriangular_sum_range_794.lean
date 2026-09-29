-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_794
-- name    : FiniteTriangular.sum_range_794
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:30.508065+00:00
-- url     : https://prove2.me/theorems/ec037e08-cd7d-474a-94bd-e92888a70388
-- title:
--   Sum of integers below 794
-- statement:
--   The sum of the nonnegative integers strictly less than $794$ equals $314821$. Equivalently, $\\sum_{k=0}^{794-1} k = 794(794-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_794 : ∑ k ∈ range 794, k = 314821 := by sorry

end FiniteTriangular
