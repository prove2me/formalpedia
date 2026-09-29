-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_893
-- name    : FiniteTriangular.sum_range_893
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:56.976092+00:00
-- url     : https://prove2.me/theorems/ac8ed88f-0c27-4a60-a24b-16b3f66b4f60
-- title:
--   Sum of integers below 893
-- statement:
--   The sum of the nonnegative integers strictly less than $893$ equals $398278$. Equivalently, $\\sum_{k=0}^{893-1} k = 893(893-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_893 : ∑ k ∈ range 893, k = 398278 := by sorry

end FiniteTriangular
