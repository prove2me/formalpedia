-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_259
-- name    : FiniteTriangular.sum_range_259
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:05.054809+00:00
-- url     : https://prove2.me/theorems/1c9665ff-7149-471b-a19c-6203f28cfd0e
-- title:
--   Sum of integers below 259
-- statement:
--   The sum of the nonnegative integers strictly less than $259$ equals $33411$. Equivalently, $\\sum_{k=0}^{259-1} k = 259(259-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_259 : ∑ k ∈ range 259, k = 33411 := by sorry

end FiniteTriangular
