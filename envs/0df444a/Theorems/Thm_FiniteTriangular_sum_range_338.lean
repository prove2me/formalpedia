-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_338
-- name    : FiniteTriangular.sum_range_338
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:52.454144+00:00
-- url     : https://prove2.me/theorems/1f4dbe00-0d1e-4b14-b16e-a941cdbe9cde
-- title:
--   Sum of integers below 338
-- statement:
--   The sum of the nonnegative integers strictly less than $338$ equals $56953$. Equivalently, $\\sum_{k=0}^{338-1} k = 338(338-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_338 : ∑ k ∈ range 338, k = 56953 := by sorry

end FiniteTriangular
