-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_809
-- name    : FiniteTriangular.sum_range_809
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:54.373889+00:00
-- url     : https://prove2.me/theorems/b76e1c5e-1b0d-48f0-816f-57393e0831b0
-- title:
--   Sum of integers below 809
-- statement:
--   The sum of the nonnegative integers strictly less than $809$ equals $326836$. Equivalently, $\\sum_{k=0}^{809-1} k = 809(809-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_809 : ∑ k ∈ range 809, k = 326836 := by sorry

end FiniteTriangular
