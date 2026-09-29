-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_138
-- name    : FiniteTriangular.sum_range_138
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:01.090842+00:00
-- url     : https://prove2.me/theorems/5bd8ccc9-8ce2-47dc-bc1d-22ccf730e16b
-- title:
--   Sum of integers below 138
-- statement:
--   The sum of the nonnegative integers strictly less than $138$ equals $9453$. Equivalently, $\sum_{k=0}^{138-1} k = 138(138-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_138 : ∑ k ∈ range 138, k = 9453 := by sorry

end FiniteTriangular
