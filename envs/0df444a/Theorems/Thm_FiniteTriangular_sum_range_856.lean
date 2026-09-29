-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_856
-- name    : FiniteTriangular.sum_range_856
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:21.808864+00:00
-- url     : https://prove2.me/theorems/6b631c1f-f7eb-4c97-adfa-3a7a33a0c948
-- title:
--   Sum of integers below 856
-- statement:
--   The sum of the nonnegative integers strictly less than $856$ equals $365940$. Equivalently, $\\sum_{k=0}^{856-1} k = 856(856-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_856 : ∑ k ∈ range 856, k = 365940 := by sorry

end FiniteTriangular
