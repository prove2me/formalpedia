-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_578
-- name    : FiniteTriangular.sum_range_578
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:37.189875+00:00
-- url     : https://prove2.me/theorems/34d8cf3c-a611-49e7-b5d9-74e7d18dd213
-- title:
--   Sum of integers below 578
-- statement:
--   The sum of the nonnegative integers strictly less than $578$ equals $166753$. Equivalently, $\\sum_{k=0}^{578-1} k = 578(578-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_578 : ∑ k ∈ range 578, k = 166753 := by sorry

end FiniteTriangular
