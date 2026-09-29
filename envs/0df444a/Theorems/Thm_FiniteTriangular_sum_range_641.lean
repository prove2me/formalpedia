-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_641
-- name    : FiniteTriangular.sum_range_641
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:13.173872+00:00
-- url     : https://prove2.me/theorems/cec3ad17-015e-4817-a736-ef1c3c1798c0
-- title:
--   Sum of integers below 641
-- statement:
--   The sum of the nonnegative integers strictly less than $641$ equals $205120$. Equivalently, $\\sum_{k=0}^{641-1} k = 641(641-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_641 : ∑ k ∈ range 641, k = 205120 := by sorry

end FiniteTriangular
