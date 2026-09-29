-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_512
-- name    : FiniteTriangular.sum_range_512
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:10.420237+00:00
-- url     : https://prove2.me/theorems/b1d17d28-c229-42cc-af6a-836ca69c74cd
-- title:
--   Sum of integers below 512
-- statement:
--   The sum of the nonnegative integers strictly less than $512$ equals $130816$. Equivalently, $\\sum_{k=0}^{512-1} k = 512(512-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_512 : ∑ k ∈ range 512, k = 130816 := by sorry

end FiniteTriangular
