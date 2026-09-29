-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_651
-- name    : FiniteTriangular.sum_range_651
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:52.207452+00:00
-- url     : https://prove2.me/theorems/811ac2ed-1993-4e51-8cdc-1c9e1bd47e9a
-- title:
--   Sum of integers below 651
-- statement:
--   The sum of the nonnegative integers strictly less than $651$ equals $211575$. Equivalently, $\\sum_{k=0}^{651-1} k = 651(651-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_651 : ∑ k ∈ range 651, k = 211575 := by sorry

end FiniteTriangular
