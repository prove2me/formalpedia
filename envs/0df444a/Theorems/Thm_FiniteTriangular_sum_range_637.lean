-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_637
-- name    : FiniteTriangular.sum_range_637
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:38.8121+00:00
-- url     : https://prove2.me/theorems/0113c399-bc42-4551-b938-91932edb4a72
-- title:
--   Sum of integers below 637
-- statement:
--   The sum of the nonnegative integers strictly less than $637$ equals $202566$. Equivalently, $\\sum_{k=0}^{637-1} k = 637(637-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_637 : ∑ k ∈ range 637, k = 202566 := by sorry

end FiniteTriangular
