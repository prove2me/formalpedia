-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_777
-- name    : FiniteTriangular.sum_range_777
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:16.622893+00:00
-- url     : https://prove2.me/theorems/7f8ce26c-88ab-4c0a-8073-e1fdf24a381c
-- title:
--   Sum of integers below 777
-- statement:
--   The sum of the nonnegative integers strictly less than $777$ equals $301476$. Equivalently, $\\sum_{k=0}^{777-1} k = 777(777-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_777 : ∑ k ∈ range 777, k = 301476 := by sorry

end FiniteTriangular
