-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_747
-- name    : FiniteTriangular.sum_range_747
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:19.257466+00:00
-- url     : https://prove2.me/theorems/422dfa30-c51e-419c-b532-b909003c0613
-- title:
--   Sum of integers below 747
-- statement:
--   The sum of the nonnegative integers strictly less than $747$ equals $278631$. Equivalently, $\\sum_{k=0}^{747-1} k = 747(747-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_747 : ∑ k ∈ range 747, k = 278631 := by sorry

end FiniteTriangular
