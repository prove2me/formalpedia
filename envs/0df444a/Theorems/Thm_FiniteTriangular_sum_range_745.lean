-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_745
-- name    : FiniteTriangular.sum_range_745
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:18.789026+00:00
-- url     : https://prove2.me/theorems/1e95b51d-b94a-4a22-a247-35716550d273
-- title:
--   Sum of integers below 745
-- statement:
--   The sum of the nonnegative integers strictly less than $745$ equals $277140$. Equivalently, $\\sum_{k=0}^{745-1} k = 745(745-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_745 : ∑ k ∈ range 745, k = 277140 := by sorry

end FiniteTriangular
