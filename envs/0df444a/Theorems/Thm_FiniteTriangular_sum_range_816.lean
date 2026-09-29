-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_816
-- name    : FiniteTriangular.sum_range_816
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:56.075651+00:00
-- url     : https://prove2.me/theorems/e1c86839-9f98-4328-b2a2-f8f7a3e83749
-- title:
--   Sum of integers below 816
-- statement:
--   The sum of the nonnegative integers strictly less than $816$ equals $332520$. Equivalently, $\\sum_{k=0}^{816-1} k = 816(816-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_816 : ∑ k ∈ range 816, k = 332520 := by sorry

end FiniteTriangular
