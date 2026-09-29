-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_169
-- name    : FiniteTriangular.sum_range_169
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:19.818979+00:00
-- url     : https://prove2.me/theorems/6a979f2d-da7a-40fc-9aaf-58e6fc37ad4a
-- title:
--   Sum of integers below 169
-- statement:
--   The sum of the nonnegative integers strictly less than $169$ equals $14196$. Equivalently, $\sum_{k=0}^{169-1} k = 169(169-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_169 : ∑ k ∈ range 169, k = 14196 := by sorry

end FiniteTriangular
