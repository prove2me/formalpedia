-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_882
-- name    : FiniteTriangular.sum_range_882
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:07.12297+00:00
-- url     : https://prove2.me/theorems/fac12664-e692-46ee-81a8-ad8e7cd31644
-- title:
--   Sum of integers below 882
-- statement:
--   The sum of the nonnegative integers strictly less than $882$ equals $388521$. Equivalently, $\\sum_{k=0}^{882-1} k = 882(882-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_882 : ∑ k ∈ range 882, k = 388521 := by sorry

end FiniteTriangular
