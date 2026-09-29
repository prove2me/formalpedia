-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_64
-- name    : FiniteTriangular.sum_range_64
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:27.934254+00:00
-- url     : https://prove2.me/theorems/13b50811-1574-410d-ab4b-092445eec154
-- title:
--   Sum of integers below 64
-- statement:
--   The sum of the nonnegative integers strictly less than $64$ equals $2016$. Equivalently, $\sum_{k=0}^{64-1} k = 64(64-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_64 : ∑ k ∈ range 64, k = 2016 := by sorry

end FiniteTriangular
