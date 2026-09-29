-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_307
-- name    : FiniteTriangular.sum_range_307
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:54.232738+00:00
-- url     : https://prove2.me/theorems/6362b2a6-7bab-4cf5-b1a4-23b0cdc0423a
-- title:
--   Sum of integers below 307
-- statement:
--   The sum of the nonnegative integers strictly less than $307$ equals $46971$. Equivalently, $\\sum_{k=0}^{307-1} k = 307(307-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_307 : ∑ k ∈ range 307, k = 46971 := by sorry

end FiniteTriangular
