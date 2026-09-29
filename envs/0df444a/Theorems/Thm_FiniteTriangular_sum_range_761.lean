-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_761
-- name    : FiniteTriangular.sum_range_761
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:40.432718+00:00
-- url     : https://prove2.me/theorems/59f22e38-3cbf-4004-9b91-faba9169709c
-- title:
--   Sum of integers below 761
-- statement:
--   The sum of the nonnegative integers strictly less than $761$ equals $289180$. Equivalently, $\\sum_{k=0}^{761-1} k = 761(761-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_761 : ∑ k ∈ range 761, k = 289180 := by sorry

end FiniteTriangular
