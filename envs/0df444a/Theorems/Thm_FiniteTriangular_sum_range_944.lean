-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_944
-- name    : FiniteTriangular.sum_range_944
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:57:01.894067+00:00
-- url     : https://prove2.me/theorems/f3472248-070a-4762-abab-85abd925d8a3
-- title:
--   Sum of integers below 944
-- statement:
--   The sum of the nonnegative integers strictly less than $944$ equals $445096$. Equivalently, $\\sum_{k=0}^{944-1} k = 944(944-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_944 : ∑ k ∈ range 944, k = 445096 := by sorry

end FiniteTriangular
