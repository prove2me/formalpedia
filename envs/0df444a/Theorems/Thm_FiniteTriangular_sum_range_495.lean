-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_495
-- name    : FiniteTriangular.sum_range_495
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:47.318441+00:00
-- url     : https://prove2.me/theorems/9c5a0051-b2c9-432a-abdf-920a9aaeaee3
-- title:
--   Sum of integers below 495
-- statement:
--   The sum of the nonnegative integers strictly less than $495$ equals $122265$. Equivalently, $\\sum_{k=0}^{495-1} k = 495(495-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_495 : ∑ k ∈ range 495, k = 122265 := by sorry

end FiniteTriangular
