-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_912
-- name    : FiniteTriangular.sum_range_912
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:11.236102+00:00
-- url     : https://prove2.me/theorems/4c978dad-440a-4e54-a31f-3124bcbde657
-- title:
--   Sum of integers below 912
-- statement:
--   The sum of the nonnegative integers strictly less than $912$ equals $415416$. Equivalently, $\\sum_{k=0}^{912-1} k = 912(912-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_912 : ∑ k ∈ range 912, k = 415416 := by sorry

end FiniteTriangular
