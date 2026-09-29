-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_865
-- name    : FiniteTriangular.sum_range_865
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:48.576417+00:00
-- url     : https://prove2.me/theorems/d5a2285f-2828-4b44-b449-4f30e4d4d2f7
-- title:
--   Sum of integers below 865
-- statement:
--   The sum of the nonnegative integers strictly less than $865$ equals $373680$. Equivalently, $\\sum_{k=0}^{865-1} k = 865(865-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_865 : ∑ k ∈ range 865, k = 373680 := by sorry

end FiniteTriangular
