-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_778
-- name    : FiniteTriangular.sum_range_778
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:09.185836+00:00
-- url     : https://prove2.me/theorems/9824e25e-6580-49cf-a6ba-24dcb80348f3
-- title:
--   Sum of integers below 778
-- statement:
--   The sum of the nonnegative integers strictly less than $778$ equals $302253$. Equivalently, $\\sum_{k=0}^{778-1} k = 778(778-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_778 : ∑ k ∈ range 778, k = 302253 := by sorry

end FiniteTriangular
