-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_617
-- name    : FiniteTriangular.sum_range_617
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:09.387914+00:00
-- url     : https://prove2.me/theorems/2addff81-a2eb-490f-aa05-746e8c6cf825
-- title:
--   Sum of integers below 617
-- statement:
--   The sum of the nonnegative integers strictly less than $617$ equals $190036$. Equivalently, $\\sum_{k=0}^{617-1} k = 617(617-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_617 : ∑ k ∈ range 617, k = 190036 := by sorry

end FiniteTriangular
