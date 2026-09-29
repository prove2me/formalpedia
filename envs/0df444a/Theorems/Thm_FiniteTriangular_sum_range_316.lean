-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_316
-- name    : FiniteTriangular.sum_range_316
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:30:27.045722+00:00
-- url     : https://prove2.me/theorems/846b5617-3096-444f-8bdb-930ead3cd965
-- title:
--   Sum of integers below 316
-- statement:
--   The sum of the nonnegative integers strictly less than $316$ equals $49770$. Equivalently, $\\sum_{k=0}^{316-1} k = 316(316-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_316 : ∑ k ∈ range 316, k = 49770 := by sorry

end FiniteTriangular
