-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_575
-- name    : FiniteTriangular.sum_range_575
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:42.552665+00:00
-- url     : https://prove2.me/theorems/556aa2bc-d97f-4dc3-ae7f-1931b0e7b58e
-- title:
--   Sum of integers below 575
-- statement:
--   The sum of the nonnegative integers strictly less than $575$ equals $165025$. Equivalently, $\\sum_{k=0}^{575-1} k = 575(575-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_575 : ∑ k ∈ range 575, k = 165025 := by sorry

end FiniteTriangular
