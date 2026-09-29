-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_16
-- name    : FiniteTriangular.sum_range_16
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:04:02.166988+00:00
-- url     : https://prove2.me/theorems/6081a07e-e9b5-432b-9f5a-38f9c887df1b
-- title:
--   Sum of integers below 16
-- statement:
--   The sum of the nonnegative integers strictly less than $16$ equals $120$. Equivalently, $\sum_{k=0}^{16-1} k = 16(16-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_16 : ∑ k ∈ range 16, k = 120 := by sorry

end FiniteTriangular
