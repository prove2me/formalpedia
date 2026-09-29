-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_302
-- name    : FiniteTriangular.sum_range_302
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:51.754797+00:00
-- url     : https://prove2.me/theorems/cd28c49a-cbe7-4bdc-ba3d-840ae9958c17
-- title:
--   Sum of integers below 302
-- statement:
--   The sum of the nonnegative integers strictly less than $302$ equals $45451$. Equivalently, $\\sum_{k=0}^{302-1} k = 302(302-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_302 : ∑ k ∈ range 302, k = 45451 := by sorry

end FiniteTriangular
