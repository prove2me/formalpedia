-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_158
-- name    : FiniteTriangular.sum_range_158
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:21.886258+00:00
-- url     : https://prove2.me/theorems/a7466ef7-d0fe-466d-8f09-1953a60f89e1
-- title:
--   Sum of integers below 158
-- statement:
--   The sum of the nonnegative integers strictly less than $158$ equals $12403$. Equivalently, $\sum_{k=0}^{158-1} k = 158(158-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_158 : ∑ k ∈ range 158, k = 12403 := by sorry

end FiniteTriangular
