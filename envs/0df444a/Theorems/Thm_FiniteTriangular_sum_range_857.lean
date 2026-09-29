-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_857
-- name    : FiniteTriangular.sum_range_857
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:58.213414+00:00
-- url     : https://prove2.me/theorems/fec97746-9c75-4b99-a5fd-11bf4caa8a6f
-- title:
--   Sum of integers below 857
-- statement:
--   The sum of the nonnegative integers strictly less than $857$ equals $366796$. Equivalently, $\\sum_{k=0}^{857-1} k = 857(857-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_857 : ∑ k ∈ range 857, k = 366796 := by sorry

end FiniteTriangular
