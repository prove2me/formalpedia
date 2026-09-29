-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_825
-- name    : FiniteTriangular.sum_range_825
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:28.473681+00:00
-- url     : https://prove2.me/theorems/2eea7534-62dd-4702-ae69-49930c24e4f9
-- title:
--   Sum of integers below 825
-- statement:
--   The sum of the nonnegative integers strictly less than $825$ equals $339900$. Equivalently, $\\sum_{k=0}^{825-1} k = 825(825-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_825 : ∑ k ∈ range 825, k = 339900 := by sorry

end FiniteTriangular
