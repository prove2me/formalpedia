-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_961
-- name    : FiniteTriangular.sum_range_961
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:36.402482+00:00
-- url     : https://prove2.me/theorems/d31aa020-d1ff-414e-8ca9-9af3e2fc3702
-- title:
--   Sum of integers below 961
-- statement:
--   The sum of the nonnegative integers strictly less than $961$ equals $461280$. Equivalently, $\\sum_{k=0}^{961-1} k = 961(961-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_961 : ∑ k ∈ range 961, k = 461280 := by sorry

end FiniteTriangular
