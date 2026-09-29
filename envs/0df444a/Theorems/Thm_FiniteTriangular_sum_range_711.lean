-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_711
-- name    : FiniteTriangular.sum_range_711
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:45.514357+00:00
-- url     : https://prove2.me/theorems/e5f3cb02-318b-4ed3-811e-15b5b434bbb9
-- title:
--   Sum of integers below 711
-- statement:
--   The sum of the nonnegative integers strictly less than $711$ equals $252405$. Equivalently, $\\sum_{k=0}^{711-1} k = 711(711-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_711 : ∑ k ∈ range 711, k = 252405 := by sorry

end FiniteTriangular
