-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_552
-- name    : FiniteTriangular.sum_range_552
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:44.555734+00:00
-- url     : https://prove2.me/theorems/971ab77b-c380-4256-900e-3e5101837e76
-- title:
--   Sum of integers below 552
-- statement:
--   The sum of the nonnegative integers strictly less than $552$ equals $152076$. Equivalently, $\\sum_{k=0}^{552-1} k = 552(552-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_552 : ∑ k ∈ range 552, k = 152076 := by sorry

end FiniteTriangular
