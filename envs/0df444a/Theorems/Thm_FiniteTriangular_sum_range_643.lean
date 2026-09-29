-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_643
-- name    : FiniteTriangular.sum_range_643
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:12.101698+00:00
-- url     : https://prove2.me/theorems/298d2bac-3d73-4e7e-8eaf-7a8262f2f826
-- title:
--   Sum of integers below 643
-- statement:
--   The sum of the nonnegative integers strictly less than $643$ equals $206403$. Equivalently, $\\sum_{k=0}^{643-1} k = 643(643-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_643 : ∑ k ∈ range 643, k = 206403 := by sorry

end FiniteTriangular
