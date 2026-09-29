-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_255
-- name    : FiniteTriangular.sum_range_255
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:01.972772+00:00
-- url     : https://prove2.me/theorems/eb759788-e57e-4933-9010-77370217b7a3
-- title:
--   Sum of integers below 255
-- statement:
--   The sum of the nonnegative integers strictly less than $255$ equals $32385$. Equivalently, $\\sum_{k=0}^{255-1} k = 255(255-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_255 : ∑ k ∈ range 255, k = 32385 := by sorry

end FiniteTriangular
