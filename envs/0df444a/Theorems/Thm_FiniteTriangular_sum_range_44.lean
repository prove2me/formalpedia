-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_44
-- name    : FiniteTriangular.sum_range_44
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:10.724987+00:00
-- url     : https://prove2.me/theorems/a8ae99ac-9d6e-46aa-b8a2-cb8060adf1be
-- title:
--   Sum of integers below 44
-- statement:
--   The sum of the nonnegative integers strictly less than $44$ equals $946$. Equivalently, $\sum_{k=0}^{44-1} k = 44(44-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_44 : ∑ k ∈ range 44, k = 946 := by sorry

end FiniteTriangular
