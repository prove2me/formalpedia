-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_187
-- name    : FiniteTriangular.sum_range_187
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:11.029683+00:00
-- url     : https://prove2.me/theorems/f6f65e59-da60-453d-9c96-656e6489686f
-- title:
--   Sum of integers below 187
-- statement:
--   The sum of the nonnegative integers strictly less than $187$ equals $17391$. Equivalently, $\\sum_{k=0}^{187-1} k = 187(187-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_187 : ∑ k ∈ range 187, k = 17391 := by sorry

end FiniteTriangular
