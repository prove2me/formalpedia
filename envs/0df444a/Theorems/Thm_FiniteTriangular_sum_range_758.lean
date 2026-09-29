-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_758
-- name    : FiniteTriangular.sum_range_758
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:57.220642+00:00
-- url     : https://prove2.me/theorems/1f4fee68-9ddf-48be-b839-7543b4679010
-- title:
--   Sum of integers below 758
-- statement:
--   The sum of the nonnegative integers strictly less than $758$ equals $286903$. Equivalently, $\\sum_{k=0}^{758-1} k = 758(758-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_758 : ∑ k ∈ range 758, k = 286903 := by sorry

end FiniteTriangular
