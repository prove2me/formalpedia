-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_776
-- name    : FiniteTriangular.sum_range_776
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:31.067395+00:00
-- url     : https://prove2.me/theorems/f8d16aa9-9879-4fcc-96f6-fe1e0b3c4dd1
-- title:
--   Sum of integers below 776
-- statement:
--   The sum of the nonnegative integers strictly less than $776$ equals $300700$. Equivalently, $\\sum_{k=0}^{776-1} k = 776(776-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_776 : ∑ k ∈ range 776, k = 300700 := by sorry

end FiniteTriangular
