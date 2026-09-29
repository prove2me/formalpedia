-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_130
-- name    : FiniteTriangular.sum_range_130
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:47.738679+00:00
-- url     : https://prove2.me/theorems/87e39d86-a92d-4f65-894c-83574f255e8d
-- title:
--   Sum of integers below 130
-- statement:
--   The sum of the nonnegative integers strictly less than $130$ equals $8385$. Equivalently, $\sum_{k=0}^{130-1} k = 130(130-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_130 : ∑ k ∈ range 130, k = 8385 := by sorry

end FiniteTriangular
