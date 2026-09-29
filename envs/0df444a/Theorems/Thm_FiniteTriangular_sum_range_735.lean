-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_735
-- name    : FiniteTriangular.sum_range_735
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:35.333583+00:00
-- url     : https://prove2.me/theorems/153a0f5e-e4df-4f52-847e-c04ff82ad980
-- title:
--   Sum of integers below 735
-- statement:
--   The sum of the nonnegative integers strictly less than $735$ equals $269745$. Equivalently, $\\sum_{k=0}^{735-1} k = 735(735-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_735 : ∑ k ∈ range 735, k = 269745 := by sorry

end FiniteTriangular
