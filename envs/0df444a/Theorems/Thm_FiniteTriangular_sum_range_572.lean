-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_572
-- name    : FiniteTriangular.sum_range_572
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:43.641601+00:00
-- url     : https://prove2.me/theorems/59f40c43-65e2-498e-a576-9905251c8ddf
-- title:
--   Sum of integers below 572
-- statement:
--   The sum of the nonnegative integers strictly less than $572$ equals $163306$. Equivalently, $\\sum_{k=0}^{572-1} k = 572(572-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_572 : ∑ k ∈ range 572, k = 163306 := by sorry

end FiniteTriangular
