-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_853
-- name    : FiniteTriangular.sum_range_853
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:21.623836+00:00
-- url     : https://prove2.me/theorems/1cd72bd5-5b04-4167-b9a7-3c0cf5461d04
-- title:
--   Sum of integers below 853
-- statement:
--   The sum of the nonnegative integers strictly less than $853$ equals $363378$. Equivalently, $\\sum_{k=0}^{853-1} k = 853(853-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_853 : ∑ k ∈ range 853, k = 363378 := by sorry

end FiniteTriangular
