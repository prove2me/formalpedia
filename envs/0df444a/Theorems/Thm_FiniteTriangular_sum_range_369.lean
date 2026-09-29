-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_369
-- name    : FiniteTriangular.sum_range_369
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:05.953845+00:00
-- url     : https://prove2.me/theorems/d5917fdf-f153-4cac-a214-068fc8a7e30d
-- title:
--   Sum of integers below 369
-- statement:
--   The sum of the nonnegative integers strictly less than $369$ equals $67896$. Equivalently, $\\sum_{k=0}^{369-1} k = 369(369-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_369 : ∑ k ∈ range 369, k = 67896 := by sorry

end FiniteTriangular
