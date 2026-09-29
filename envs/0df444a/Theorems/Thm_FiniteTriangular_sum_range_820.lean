-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_820
-- name    : FiniteTriangular.sum_range_820
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:44.593501+00:00
-- url     : https://prove2.me/theorems/fb1762fa-90f5-4e09-ae98-c14eb897de78
-- title:
--   Sum of integers below 820
-- statement:
--   The sum of the nonnegative integers strictly less than $820$ equals $335790$. Equivalently, $\\sum_{k=0}^{820-1} k = 820(820-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_820 : ∑ k ∈ range 820, k = 335790 := by sorry

end FiniteTriangular
