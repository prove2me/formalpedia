-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_419
-- name    : FiniteTriangular.sum_range_419
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:54.706629+00:00
-- url     : https://prove2.me/theorems/7ea06184-be87-4ef0-870e-0fd0c51c2841
-- title:
--   Sum of integers below 419
-- statement:
--   The sum of the nonnegative integers strictly less than $419$ equals $87571$. Equivalently, $\\sum_{k=0}^{419-1} k = 419(419-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_419 : ∑ k ∈ range 419, k = 87571 := by sorry

end FiniteTriangular
