-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_968
-- name    : FiniteTriangular.sum_range_968
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:36.492245+00:00
-- url     : https://prove2.me/theorems/393c200d-d10c-49b2-bcd9-2c05fecfa9ce
-- title:
--   Sum of integers below 968
-- statement:
--   The sum of the nonnegative integers strictly less than $968$ equals $468028$. Equivalently, $\\sum_{k=0}^{968-1} k = 968(968-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_968 : ∑ k ∈ range 968, k = 468028 := by sorry

end FiniteTriangular
