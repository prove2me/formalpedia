-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_323
-- name    : FiniteTriangular.sum_range_323
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:10.813844+00:00
-- url     : https://prove2.me/theorems/efd9ddf5-099d-4583-b257-1b8f8cc60e3c
-- title:
--   Sum of integers below 323
-- statement:
--   The sum of the nonnegative integers strictly less than $323$ equals $52003$. Equivalently, $\\sum_{k=0}^{323-1} k = 323(323-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_323 : ∑ k ∈ range 323, k = 52003 := by sorry

end FiniteTriangular
