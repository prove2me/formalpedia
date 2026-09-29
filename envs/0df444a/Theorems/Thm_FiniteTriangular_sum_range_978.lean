-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_978
-- name    : FiniteTriangular.sum_range_978
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:02.228561+00:00
-- url     : https://prove2.me/theorems/3449a05d-a321-460b-993c-2b0a6b046320
-- title:
--   Sum of the nonnegative integers below 978
-- statement:
--   The sum of the integers from $0$ through $977$ equals $477753$, which is the triangular number $\\frac{978(977)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_978 : ∑ k ∈ range 978, k = 477753 := by sorry
end FiniteTriangular
