-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_483
-- name    : FiniteTriangular.sum_range_483
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:09.974434+00:00
-- url     : https://prove2.me/theorems/2ecf1e2c-e8e7-49af-8824-29b72480ae65
-- title:
--   Sum of integers below 483
-- statement:
--   The sum of the nonnegative integers strictly less than $483$ equals $116403$. Equivalently, $\\sum_{k=0}^{483-1} k = 483(483-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_483 : ∑ k ∈ range 483, k = 116403 := by sorry

end FiniteTriangular
