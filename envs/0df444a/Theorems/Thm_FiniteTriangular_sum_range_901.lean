-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_901
-- name    : FiniteTriangular.sum_range_901
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:36.28033+00:00
-- url     : https://prove2.me/theorems/fa2e2cbe-3a76-4151-b743-2e91282c6c45
-- title:
--   Sum of integers below 901
-- statement:
--   The sum of the nonnegative integers strictly less than $901$ equals $405450$. Equivalently, $\\sum_{k=0}^{901-1} k = 901(901-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_901 : ∑ k ∈ range 901, k = 405450 := by sorry

end FiniteTriangular
