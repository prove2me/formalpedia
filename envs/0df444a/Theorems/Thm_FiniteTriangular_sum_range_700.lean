-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_700
-- name    : FiniteTriangular.sum_range_700
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:58.675434+00:00
-- url     : https://prove2.me/theorems/524b8a24-147f-4cae-a6ea-7040bb7741e4
-- title:
--   Sum of integers below 700
-- statement:
--   The sum of the nonnegative integers strictly less than $700$ equals $244650$. Equivalently, $\\sum_{k=0}^{700-1} k = 700(700-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_700 : ∑ k ∈ range 700, k = 244650 := by sorry

end FiniteTriangular
