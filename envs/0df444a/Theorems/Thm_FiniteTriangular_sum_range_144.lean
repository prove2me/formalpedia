-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_144
-- name    : FiniteTriangular.sum_range_144
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:56:59.176679+00:00
-- url     : https://prove2.me/theorems/5c778290-f749-444e-bedb-23a23ddbc4a3
-- title:
--   Sum of integers below 144
-- statement:
--   The sum of the nonnegative integers strictly less than $144$ equals $10296$. Equivalently, $\sum_{k=0}^{144-1} k = 144(144-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_144 : ∑ k ∈ range 144, k = 10296 := by sorry

end FiniteTriangular
