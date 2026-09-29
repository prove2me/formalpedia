-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_355
-- name    : FiniteTriangular.sum_range_355
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:19.206189+00:00
-- url     : https://prove2.me/theorems/47ca280b-3ccd-4f22-b50d-d7a900356522
-- title:
--   Sum of integers below 355
-- statement:
--   The sum of the nonnegative integers strictly less than $355$ equals $62835$. Equivalently, $\\sum_{k=0}^{355-1} k = 355(355-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_355 : ∑ k ∈ range 355, k = 62835 := by sorry

end FiniteTriangular
