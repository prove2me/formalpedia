-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_56
-- name    : FiniteTriangular.sum_range_56
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:19:02.878413+00:00
-- url     : https://prove2.me/theorems/b204abdb-b5de-4bcc-9d80-bebfd50af162
-- title:
--   Sum of integers below 56
-- statement:
--   The sum of the nonnegative integers strictly less than $56$ equals $1540$. Equivalently, $\sum_{k=0}^{56-1} k = 56(56-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_56 : ∑ k ∈ range 56, k = 1540 := by sorry

end FiniteTriangular
