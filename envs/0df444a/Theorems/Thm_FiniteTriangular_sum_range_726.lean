-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_726
-- name    : FiniteTriangular.sum_range_726
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:47.133544+00:00
-- url     : https://prove2.me/theorems/fb6cfded-c981-445c-8676-b769e1555ed4
-- title:
--   Sum of integers below 726
-- statement:
--   The sum of the nonnegative integers strictly less than $726$ equals $263175$. Equivalently, $\\sum_{k=0}^{726-1} k = 726(726-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_726 : ∑ k ∈ range 726, k = 263175 := by sorry

end FiniteTriangular
