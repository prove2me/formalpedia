-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_863
-- name    : FiniteTriangular.sum_range_863
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:40:00.420873+00:00
-- url     : https://prove2.me/theorems/983a8827-1cf8-4a22-a107-837ee01b9beb
-- title:
--   Sum of integers below 863
-- statement:
--   The sum of the nonnegative integers strictly less than $863$ equals $371953$. Equivalently, $\\sum_{k=0}^{863-1} k = 863(863-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_863 : ∑ k ∈ range 863, k = 371953 := by sorry

end FiniteTriangular
