-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_404
-- name    : FiniteTriangular.sum_range_404
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:23.540888+00:00
-- url     : https://prove2.me/theorems/13a63614-2d7e-4a4b-8104-e0daeaba4632
-- title:
--   Sum of integers below 404
-- statement:
--   The sum of the nonnegative integers strictly less than $404$ equals $81406$. Equivalently, $\\sum_{k=0}^{404-1} k = 404(404-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_404 : ∑ k ∈ range 404, k = 81406 := by sorry

end FiniteTriangular
