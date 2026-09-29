-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_451
-- name    : FiniteTriangular.sum_range_451
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:50.308379+00:00
-- url     : https://prove2.me/theorems/aff43c4d-38aa-4a77-b068-167320059b67
-- title:
--   Sum of integers below 451
-- statement:
--   The sum of the nonnegative integers strictly less than $451$ equals $101475$. Equivalently, $\\sum_{k=0}^{451-1} k = 451(451-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_451 : ∑ k ∈ range 451, k = 101475 := by sorry

end FiniteTriangular
