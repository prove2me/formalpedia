-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_311
-- name    : FiniteTriangular.sum_range_311
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:53.15228+00:00
-- url     : https://prove2.me/theorems/60e1d713-142e-4cee-9f29-b89147399644
-- title:
--   Sum of integers below 311
-- statement:
--   The sum of the nonnegative integers strictly less than $311$ equals $48205$. Equivalently, $\\sum_{k=0}^{311-1} k = 311(311-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_311 : ∑ k ∈ range 311, k = 48205 := by sorry

end FiniteTriangular
