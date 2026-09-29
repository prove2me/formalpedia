-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_489
-- name    : FiniteTriangular.sum_range_489
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:46.660099+00:00
-- url     : https://prove2.me/theorems/071637d4-b5fa-4f0e-80fa-ac209d1d934d
-- title:
--   Sum of integers below 489
-- statement:
--   The sum of the nonnegative integers strictly less than $489$ equals $119316$. Equivalently, $\\sum_{k=0}^{489-1} k = 489(489-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_489 : ∑ k ∈ range 489, k = 119316 := by sorry

end FiniteTriangular
