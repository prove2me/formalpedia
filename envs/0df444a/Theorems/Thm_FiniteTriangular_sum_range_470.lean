-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_470
-- name    : FiniteTriangular.sum_range_470
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:40.081772+00:00
-- url     : https://prove2.me/theorems/b1e33f3c-ca30-4e3e-afdc-d0cdff8bae73
-- title:
--   Sum of integers below 470
-- statement:
--   The sum of the nonnegative integers strictly less than $470$ equals $110215$. Equivalently, $\\sum_{k=0}^{470-1} k = 470(470-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_470 : ∑ k ∈ range 470, k = 110215 := by sorry

end FiniteTriangular
