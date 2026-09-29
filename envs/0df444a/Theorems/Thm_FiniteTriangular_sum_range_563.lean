-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_563
-- name    : FiniteTriangular.sum_range_563
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:08.312308+00:00
-- url     : https://prove2.me/theorems/c2101c38-8a62-4e08-bfb9-754dd0f91942
-- title:
--   Sum of integers below 563
-- statement:
--   The sum of the nonnegative integers strictly less than $563$ equals $158203$. Equivalently, $\\sum_{k=0}^{563-1} k = 563(563-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_563 : ∑ k ∈ range 563, k = 158203 := by sorry

end FiniteTriangular
