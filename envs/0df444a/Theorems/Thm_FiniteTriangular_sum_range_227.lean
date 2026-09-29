-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_227
-- name    : FiniteTriangular.sum_range_227
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:04.642719+00:00
-- url     : https://prove2.me/theorems/3a978abc-2bc0-493c-93e0-a24bd3f92c23
-- title:
--   Sum of integers below 227
-- statement:
--   The sum of the nonnegative integers strictly less than $227$ equals $25651$. Equivalently, $\\sum_{k=0}^{227-1} k = 227(227-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_227 : ∑ k ∈ range 227, k = 25651 := by sorry

end FiniteTriangular
