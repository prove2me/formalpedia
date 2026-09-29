-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_963
-- name    : FiniteTriangular.sum_range_963
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:35.790913+00:00
-- url     : https://prove2.me/theorems/885dbb4f-c61c-446d-ae32-03f8c83b9526
-- title:
--   Sum of integers below 963
-- statement:
--   The sum of the nonnegative integers strictly less than $963$ equals $463203$. Equivalently, $\\sum_{k=0}^{963-1} k = 963(963-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_963 : ∑ k ∈ range 963, k = 463203 := by sorry

end FiniteTriangular
