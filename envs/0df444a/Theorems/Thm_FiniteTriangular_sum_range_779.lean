-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_779
-- name    : FiniteTriangular.sum_range_779
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:14.185098+00:00
-- url     : https://prove2.me/theorems/caa9eecf-9c17-43ef-a1c9-99d947b186b2
-- title:
--   Sum of integers below 779
-- statement:
--   The sum of the nonnegative integers strictly less than $779$ equals $303031$. Equivalently, $\\sum_{k=0}^{779-1} k = 779(779-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_779 : ∑ k ∈ range 779, k = 303031 := by sorry

end FiniteTriangular
