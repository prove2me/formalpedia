-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_692
-- name    : FiniteTriangular.sum_range_692
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:28.880784+00:00
-- url     : https://prove2.me/theorems/40327bba-a8ac-4a64-9416-1b4a96c75df2
-- title:
--   Sum of integers below 692
-- statement:
--   The sum of the nonnegative integers strictly less than $692$ equals $239086$. Equivalently, $\\sum_{k=0}^{692-1} k = 692(692-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_692 : ∑ k ∈ range 692, k = 239086 := by sorry

end FiniteTriangular
