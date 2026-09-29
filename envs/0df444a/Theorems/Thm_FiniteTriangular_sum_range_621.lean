-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_621
-- name    : FiniteTriangular.sum_range_621
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:08.698393+00:00
-- url     : https://prove2.me/theorems/f6bc3ee7-3a5e-4671-bb66-ffe7ce47a7d0
-- title:
--   Sum of integers below 621
-- statement:
--   The sum of the nonnegative integers strictly less than $621$ equals $192510$. Equivalently, $\\sum_{k=0}^{621-1} k = 621(621-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_621 : ∑ k ∈ range 621, k = 192510 := by sorry

end FiniteTriangular
