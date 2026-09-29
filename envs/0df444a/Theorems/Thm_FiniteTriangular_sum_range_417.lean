-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_417
-- name    : FiniteTriangular.sum_range_417
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:49.887038+00:00
-- url     : https://prove2.me/theorems/deba1ba9-9012-4534-8cfa-db668c2a41f2
-- title:
--   Sum of integers below 417
-- statement:
--   The sum of the nonnegative integers strictly less than $417$ equals $86736$. Equivalently, $\\sum_{k=0}^{417-1} k = 417(417-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_417 : ∑ k ∈ range 417, k = 86736 := by sorry

end FiniteTriangular
