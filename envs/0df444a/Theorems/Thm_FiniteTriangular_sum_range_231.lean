-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_231
-- name    : FiniteTriangular.sum_range_231
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:03.018408+00:00
-- url     : https://prove2.me/theorems/6440f7b8-c7b2-4854-9970-bfd2a3ba93d5
-- title:
--   Sum of integers below 231
-- statement:
--   The sum of the nonnegative integers strictly less than $231$ equals $26565$. Equivalently, $\\sum_{k=0}^{231-1} k = 231(231-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_231 : ∑ k ∈ range 231, k = 26565 := by sorry

end FiniteTriangular
