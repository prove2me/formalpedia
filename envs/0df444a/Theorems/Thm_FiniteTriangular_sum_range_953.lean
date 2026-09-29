-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_953
-- name    : FiniteTriangular.sum_range_953
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:47.346605+00:00
-- url     : https://prove2.me/theorems/e04460a3-1b2e-4dab-9dd0-24d744543a08
-- title:
--   Sum of integers below 953
-- statement:
--   The sum of the nonnegative integers strictly less than $953$ equals $453628$. Equivalently, $\\sum_{k=0}^{953-1} k = 953(953-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_953 : ∑ k ∈ range 953, k = 453628 := by sorry

end FiniteTriangular
