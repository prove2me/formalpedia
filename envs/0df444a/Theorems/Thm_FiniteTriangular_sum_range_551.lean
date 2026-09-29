-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_551
-- name    : FiniteTriangular.sum_range_551
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:43.469423+00:00
-- url     : https://prove2.me/theorems/20fca31f-cc21-4cdd-83dc-1afb70d3cb28
-- title:
--   Sum of integers below 551
-- statement:
--   The sum of the nonnegative integers strictly less than $551$ equals $151525$. Equivalently, $\\sum_{k=0}^{551-1} k = 551(551-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_551 : ∑ k ∈ range 551, k = 151525 := by sorry

end FiniteTriangular
