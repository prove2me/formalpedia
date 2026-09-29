-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_843
-- name    : FiniteTriangular.sum_range_843
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:42.762346+00:00
-- url     : https://prove2.me/theorems/21505cbc-7204-4b55-b66c-8c4eff26a405
-- title:
--   Sum of integers below 843
-- statement:
--   The sum of the nonnegative integers strictly less than $843$ equals $354903$. Equivalently, $\\sum_{k=0}^{843-1} k = 843(843-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_843 : ∑ k ∈ range 843, k = 354903 := by sorry

end FiniteTriangular
