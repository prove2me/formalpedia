-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_573
-- name    : FiniteTriangular.sum_range_573
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:42.855975+00:00
-- url     : https://prove2.me/theorems/2fa4c6bb-4f55-4496-973b-afdf070cbaf6
-- title:
--   Sum of integers below 573
-- statement:
--   The sum of the nonnegative integers strictly less than $573$ equals $163878$. Equivalently, $\\sum_{k=0}^{573-1} k = 573(573-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_573 : ∑ k ∈ range 573, k = 163878 := by sorry

end FiniteTriangular
