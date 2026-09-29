-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_656
-- name    : FiniteTriangular.sum_range_656
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:51.250677+00:00
-- url     : https://prove2.me/theorems/88e1f940-789b-420f-9ce6-49c7a92f14fe
-- title:
--   Sum of integers below 656
-- statement:
--   The sum of the nonnegative integers strictly less than $656$ equals $214840$. Equivalently, $\\sum_{k=0}^{656-1} k = 656(656-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_656 : ∑ k ∈ range 656, k = 214840 := by sorry

end FiniteTriangular
