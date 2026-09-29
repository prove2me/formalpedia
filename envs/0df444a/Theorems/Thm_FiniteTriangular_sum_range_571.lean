-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_571
-- name    : FiniteTriangular.sum_range_571
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:43.782328+00:00
-- url     : https://prove2.me/theorems/4f7b3a14-c8c9-4ba5-b6f4-a9a9bc29e786
-- title:
--   Sum of integers below 571
-- statement:
--   The sum of the nonnegative integers strictly less than $571$ equals $162735$. Equivalently, $\\sum_{k=0}^{571-1} k = 571(571-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_571 : ∑ k ∈ range 571, k = 162735 := by sorry

end FiniteTriangular
