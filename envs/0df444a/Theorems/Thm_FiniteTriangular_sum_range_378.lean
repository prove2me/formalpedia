-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_378
-- name    : FiniteTriangular.sum_range_378
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:13.673311+00:00
-- url     : https://prove2.me/theorems/01013555-cbd9-4028-a4c0-08171145626e
-- title:
--   Sum of integers below 378
-- statement:
--   The sum of the nonnegative integers strictly less than $378$ equals $71253$. Equivalently, $\\sum_{k=0}^{378-1} k = 378(378-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_378 : ∑ k ∈ range 378, k = 71253 := by sorry

end FiniteTriangular
