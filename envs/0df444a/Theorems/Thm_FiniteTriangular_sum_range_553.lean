-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_553
-- name    : FiniteTriangular.sum_range_553
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:18.294527+00:00
-- url     : https://prove2.me/theorems/eb0f1e40-cefd-4a91-8844-0505bb77b7c4
-- title:
--   Sum of integers below 553
-- statement:
--   The sum of the nonnegative integers strictly less than $553$ equals $152628$. Equivalently, $\\sum_{k=0}^{553-1} k = 553(553-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_553 : ∑ k ∈ range 553, k = 152628 := by sorry

end FiniteTriangular
