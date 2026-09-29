-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_689
-- name    : FiniteTriangular.sum_range_689
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:27.115963+00:00
-- url     : https://prove2.me/theorems/5e84a3b5-1df5-4260-96bd-1b68b0c883b4
-- title:
--   Sum of integers below 689
-- statement:
--   The sum of the nonnegative integers strictly less than $689$ equals $237016$. Equivalently, $\\sum_{k=0}^{689-1} k = 689(689-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_689 : ∑ k ∈ range 689, k = 237016 := by sorry

end FiniteTriangular
