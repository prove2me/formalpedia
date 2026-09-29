-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_346
-- name    : FiniteTriangular.sum_range_346
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:41.186004+00:00
-- url     : https://prove2.me/theorems/2df26eea-cf5c-42b4-a15b-01680342f195
-- title:
--   Sum of integers below 346
-- statement:
--   The sum of the nonnegative integers strictly less than $346$ equals $59685$. Equivalently, $\\sum_{k=0}^{346-1} k = 346(346-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_346 : ∑ k ∈ range 346, k = 59685 := by sorry

end FiniteTriangular
