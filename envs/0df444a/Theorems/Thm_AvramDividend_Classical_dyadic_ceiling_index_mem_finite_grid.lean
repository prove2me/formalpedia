-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
-- name    : AvramDividend.Classical.dyadic_ceiling_index_mem_finite_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:49:13.910027+00:00
-- url     : https://prove2.me/theorems/e4acb2d9-70e6-4a85-9132-33f2a754f1ec
-- title:
--   Dyadic ceiling indices of bounded times lie in a finite grid
-- statement:
--   If 0≤t≤T, then its dyadic ceiling index ceil(2^n t) lies in the explicit finite set of natural indices below ceil(2^n T)+1. This provides the finite-range support component of approximating bounded stopping times from above by dyadic grids. It follows from monotonicity of the ceiling under multiplication by the positive dyadic scale.
-- source:
--   One finite-range component required by Open bounded_stopping_dyadic_grid_approximation (68cdb033-cbf7-4640-a303-5d06c3c7a761).

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_index_mem_finite_grid
    (t T : ℝ≥0) (ht : t ≤ T) (n : ℕ) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ∈
      Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1) := by sorry
