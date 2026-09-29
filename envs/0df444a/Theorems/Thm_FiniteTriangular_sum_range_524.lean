-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_524
-- name    : FiniteTriangular.sum_range_524
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:39.852168+00:00
-- url     : https://prove2.me/theorems/1d94824e-e1c1-47f6-9434-930b4f59bb6d
-- title:
--   Sum of integers below 524
-- statement:
--   The sum of the nonnegative integers strictly less than $524$ equals $137026$. Equivalently, $\\sum_{k=0}^{524-1} k = 524(524-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_524 : ∑ k ∈ range 524, k = 137026 := by sorry

end FiniteTriangular
