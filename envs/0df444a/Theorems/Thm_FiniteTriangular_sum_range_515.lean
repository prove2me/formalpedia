-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_515
-- name    : FiniteTriangular.sum_range_515
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:53.467799+00:00
-- url     : https://prove2.me/theorems/7eeb380c-d797-4458-8188-92f9108386ab
-- title:
--   Sum of integers below 515
-- statement:
--   The sum of the nonnegative integers strictly less than $515$ equals $132355$. Equivalently, $\\sum_{k=0}^{515-1} k = 515(515-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_515 : ∑ k ∈ range 515, k = 132355 := by sorry

end FiniteTriangular
