-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_256
-- name    : FiniteTriangular.sum_range_256
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:04.10203+00:00
-- url     : https://prove2.me/theorems/adda54b3-bf1c-4d3c-a67e-fbe66172539c
-- title:
--   Sum of integers below 256
-- statement:
--   The sum of the nonnegative integers strictly less than $256$ equals $32640$. Equivalently, $\\sum_{k=0}^{256-1} k = 256(256-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_256 : ∑ k ∈ range 256, k = 32640 := by sorry

end FiniteTriangular
