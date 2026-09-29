-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_74
-- name    : FiniteTriangular.sum_range_74
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:08.795987+00:00
-- url     : https://prove2.me/theorems/55ea5c40-cdfe-4a70-9d92-b7b7bbdd64fb
-- title:
--   Sum of integers below 74
-- statement:
--   The sum of the nonnegative integers strictly less than $74$ equals $2701$. Equivalently, $\sum_{k=0}^{74-1} k = 74(74-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_74 : ∑ k ∈ range 74, k = 2701 := by sorry

end FiniteTriangular
