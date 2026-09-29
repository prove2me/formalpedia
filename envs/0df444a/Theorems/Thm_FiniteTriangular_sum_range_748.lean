-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_748
-- name    : FiniteTriangular.sum_range_748
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:21.701658+00:00
-- url     : https://prove2.me/theorems/297450b2-b99e-4562-9aa4-9da9048891cb
-- title:
--   Sum of integers below 748
-- statement:
--   The sum of the nonnegative integers strictly less than $748$ equals $279378$. Equivalently, $\\sum_{k=0}^{748-1} k = 748(748-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_748 : ∑ k ∈ range 748, k = 279378 := by sorry

end FiniteTriangular
