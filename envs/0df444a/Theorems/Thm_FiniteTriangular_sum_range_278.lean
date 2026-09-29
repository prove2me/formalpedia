-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_278
-- name    : FiniteTriangular.sum_range_278
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:43.211189+00:00
-- url     : https://prove2.me/theorems/0a8fabdf-3fc9-4b8e-97d0-d447afecb76c
-- title:
--   Sum of integers below 278
-- statement:
--   The sum of the nonnegative integers strictly less than $278$ equals $38503$. Equivalently, $\\sum_{k=0}^{278-1} k = 278(278-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_278 : ∑ k ∈ range 278, k = 38503 := by sorry

end FiniteTriangular
