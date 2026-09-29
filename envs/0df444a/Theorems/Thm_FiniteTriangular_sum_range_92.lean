-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_92
-- name    : FiniteTriangular.sum_range_92
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:43.741989+00:00
-- url     : https://prove2.me/theorems/36120d1d-dc1e-469f-873a-b91d144f095a
-- title:
--   Sum of integers below 92
-- statement:
--   The sum of the nonnegative integers strictly less than $92$ equals $4186$. Equivalently, $\sum_{k=0}^{92-1} k = 92(92-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_92 : ∑ k ∈ range 92, k = 4186 := by sorry

end FiniteTriangular
