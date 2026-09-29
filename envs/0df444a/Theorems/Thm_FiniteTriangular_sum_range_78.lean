-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_78
-- name    : FiniteTriangular.sum_range_78
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:09.469101+00:00
-- url     : https://prove2.me/theorems/e28a6962-1546-4161-b067-0d667d513fec
-- title:
--   Sum of integers below 78
-- statement:
--   The sum of the nonnegative integers strictly less than $78$ equals $3003$. Equivalently, $\sum_{k=0}^{78-1} k = 78(78-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_78 : ∑ k ∈ range 78, k = 3003 := by sorry

end FiniteTriangular
