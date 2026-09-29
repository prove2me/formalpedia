-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_788
-- name    : FiniteTriangular.sum_range_788
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:55.198409+00:00
-- url     : https://prove2.me/theorems/7340f65f-3a93-4b7d-af1a-f2a7721e9faa
-- title:
--   Sum of integers below 788
-- statement:
--   The sum of the nonnegative integers strictly less than $788$ equals $310078$. Equivalently, $\\sum_{k=0}^{788-1} k = 788(788-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_788 : ∑ k ∈ range 788, k = 310078 := by sorry

end FiniteTriangular
