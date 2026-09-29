-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_724
-- name    : FiniteTriangular.sum_range_724
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:46.624538+00:00
-- url     : https://prove2.me/theorems/6162da10-189d-4573-b3d2-c66ab2180303
-- title:
--   Sum of integers below 724
-- statement:
--   The sum of the nonnegative integers strictly less than $724$ equals $261726$. Equivalently, $\\sum_{k=0}^{724-1} k = 724(724-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_724 : ∑ k ∈ range 724, k = 261726 := by sorry

end FiniteTriangular
