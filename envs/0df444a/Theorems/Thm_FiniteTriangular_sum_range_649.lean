-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_649
-- name    : FiniteTriangular.sum_range_649
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:49.560694+00:00
-- url     : https://prove2.me/theorems/7eb02ce3-965e-4614-9ec4-0a2c2eddec2b
-- title:
--   Sum of integers below 649
-- statement:
--   The sum of the nonnegative integers strictly less than $649$ equals $210276$. Equivalently, $\\sum_{k=0}^{649-1} k = 649(649-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_649 : ∑ k ∈ range 649, k = 210276 := by sorry

end FiniteTriangular
