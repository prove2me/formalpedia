-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_851
-- name    : FiniteTriangular.sum_range_851
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:20.290821+00:00
-- url     : https://prove2.me/theorems/5d0f5847-2eb0-4579-9279-309e01add278
-- title:
--   Sum of integers below 851
-- statement:
--   The sum of the nonnegative integers strictly less than $851$ equals $361675$. Equivalently, $\\sum_{k=0}^{851-1} k = 851(851-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_851 : ∑ k ∈ range 851, k = 361675 := by sorry

end FiniteTriangular
