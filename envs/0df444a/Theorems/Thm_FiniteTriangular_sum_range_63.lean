-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_63
-- name    : FiniteTriangular.sum_range_63
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:19.494118+00:00
-- url     : https://prove2.me/theorems/494ab37d-9ec7-4ed4-be49-ef5314189962
-- title:
--   Sum of integers below 63
-- statement:
--   The sum of the nonnegative integers strictly less than $63$ equals $1953$. Equivalently, $\sum_{k=0}^{63-1} k = 63(63-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_63 : ∑ k ∈ range 63, k = 1953 := by sorry

end FiniteTriangular
