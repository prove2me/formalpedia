-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_886
-- name    : FiniteTriangular.sum_range_886
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:09.944818+00:00
-- url     : https://prove2.me/theorems/e33cf978-a8b6-4a08-b967-6507b6bffe8e
-- title:
--   Sum of integers below 886
-- statement:
--   The sum of the nonnegative integers strictly less than $886$ equals $392055$. Equivalently, $\\sum_{k=0}^{886-1} k = 886(886-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_886 : ∑ k ∈ range 886, k = 392055 := by sorry

end FiniteTriangular
