-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_283
-- name    : FiniteTriangular.sum_range_283
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:28.517589+00:00
-- url     : https://prove2.me/theorems/827c959b-8bf0-4005-bc04-986c727689a0
-- title:
--   Sum of integers below 283
-- statement:
--   The sum of the nonnegative integers strictly less than $283$ equals $39903$. Equivalently, $\\sum_{k=0}^{283-1} k = 283(283-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_283 : ∑ k ∈ range 283, k = 39903 := by sorry

end FiniteTriangular
