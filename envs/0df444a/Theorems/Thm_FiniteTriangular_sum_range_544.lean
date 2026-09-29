-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_544
-- name    : FiniteTriangular.sum_range_544
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:55.288658+00:00
-- url     : https://prove2.me/theorems/2a303700-6274-46b7-8907-adbbd45c2f31
-- title:
--   Sum of integers below 544
-- statement:
--   The sum of the nonnegative integers strictly less than $544$ equals $147696$. Equivalently, $\\sum_{k=0}^{544-1} k = 544(544-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_544 : ∑ k ∈ range 544, k = 147696 := by sorry

end FiniteTriangular
