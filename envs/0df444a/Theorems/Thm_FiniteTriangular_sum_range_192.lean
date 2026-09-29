-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_192
-- name    : FiniteTriangular.sum_range_192
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:08.683873+00:00
-- url     : https://prove2.me/theorems/aa144966-ee0e-423e-8a31-068c8790d9a2
-- title:
--   Sum of integers below 192
-- statement:
--   The sum of the nonnegative integers strictly less than $192$ equals $18336$. Equivalently, $\\sum_{k=0}^{192-1} k = 192(192-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_192 : ∑ k ∈ range 192, k = 18336 := by sorry

end FiniteTriangular
