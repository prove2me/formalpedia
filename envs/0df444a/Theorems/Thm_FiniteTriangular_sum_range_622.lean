-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_622
-- name    : FiniteTriangular.sum_range_622
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:12.45199+00:00
-- url     : https://prove2.me/theorems/2e9d17dd-f0f5-4fa3-9287-ecd9c9ecb6f3
-- title:
--   Sum of integers below 622
-- statement:
--   The sum of the nonnegative integers strictly less than $622$ equals $193131$. Equivalently, $\\sum_{k=0}^{622-1} k = 622(622-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_622 : ∑ k ∈ range 622, k = 193131 := by sorry

end FiniteTriangular
