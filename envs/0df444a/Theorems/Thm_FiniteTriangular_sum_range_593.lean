-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_593
-- name    : FiniteTriangular.sum_range_593
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:43:00.169579+00:00
-- url     : https://prove2.me/theorems/a014a6ae-5671-42bd-b1b9-e60eda63ae94
-- title:
--   Sum of integers below 593
-- statement:
--   The sum of the nonnegative integers strictly less than $593$ equals $175528$. Equivalently, $\\sum_{k=0}^{593-1} k = 593(593-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_593 : ∑ k ∈ range 593, k = 175528 := by sorry

end FiniteTriangular
