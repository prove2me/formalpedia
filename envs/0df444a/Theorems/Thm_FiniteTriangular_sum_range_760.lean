-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_760
-- name    : FiniteTriangular.sum_range_760
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:18:01.246629+00:00
-- url     : https://prove2.me/theorems/ed562278-1c58-41b5-9e92-1c1f240f8a3e
-- title:
--   Sum of integers below 760
-- statement:
--   The sum of the nonnegative integers strictly less than $760$ equals $288420$. Equivalently, $\\sum_{k=0}^{760-1} k = 760(760-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_760 : ∑ k ∈ range 760, k = 288420 := by sorry

end FiniteTriangular
