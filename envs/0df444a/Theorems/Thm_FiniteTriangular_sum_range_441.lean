-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_441
-- name    : FiniteTriangular.sum_range_441
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:04.809674+00:00
-- url     : https://prove2.me/theorems/6864a581-dc0b-47e6-993a-aa7f867f1b78
-- title:
--   Sum of integers below 441
-- statement:
--   The sum of the nonnegative integers strictly less than $441$ equals $97020$. Equivalently, $\\sum_{k=0}^{441-1} k = 441(441-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_441 : ∑ k ∈ range 441, k = 97020 := by sorry

end FiniteTriangular
