-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_793
-- name    : FiniteTriangular.sum_range_793
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:31.349013+00:00
-- url     : https://prove2.me/theorems/78783d4a-335e-40c7-9396-740694226c93
-- title:
--   Sum of integers below 793
-- statement:
--   The sum of the nonnegative integers strictly less than $793$ equals $314028$. Equivalently, $\\sum_{k=0}^{793-1} k = 793(793-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_793 : ∑ k ∈ range 793, k = 314028 := by sorry

end FiniteTriangular
