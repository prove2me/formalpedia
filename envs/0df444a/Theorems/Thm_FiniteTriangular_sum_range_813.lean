-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_813
-- name    : FiniteTriangular.sum_range_813
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:53.548119+00:00
-- url     : https://prove2.me/theorems/49d551a9-85c0-4d55-8af5-7f84144ea0a5
-- title:
--   Sum of integers below 813
-- statement:
--   The sum of the nonnegative integers strictly less than $813$ equals $330078$. Equivalently, $\\sum_{k=0}^{813-1} k = 813(813-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_813 : ∑ k ∈ range 813, k = 330078 := by sorry

end FiniteTriangular
