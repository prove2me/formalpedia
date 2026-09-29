-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_96
-- name    : FiniteTriangular.sum_range_96
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:40.127825+00:00
-- url     : https://prove2.me/theorems/e1cfec1a-1e90-4631-95e9-cee24bdde3ec
-- title:
--   Sum of integers below 96
-- statement:
--   The sum of the nonnegative integers strictly less than $96$ equals $4560$. Equivalently, $\sum_{k=0}^{96-1} k = 96(96-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_96 : ∑ k ∈ range 96, k = 4560 := by sorry

end FiniteTriangular
