-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_475
-- name    : FiniteTriangular.sum_range_475
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:26.945877+00:00
-- url     : https://prove2.me/theorems/347da3e3-70f3-42c9-8711-93d66d0b3bcb
-- title:
--   Sum of integers below 475
-- statement:
--   The sum of the nonnegative integers strictly less than $475$ equals $112575$. Equivalently, $\\sum_{k=0}^{475-1} k = 475(475-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_475 : ∑ k ∈ range 475, k = 112575 := by sorry

end FiniteTriangular
