-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_ceiling_grid_preterminal_lt
-- name    : AvramDividend.Classical.chat03_ceiling_grid_preterminal_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:15:29.645926+00:00
-- url     : https://prove2.me/theorems/83b610ca-151c-4098-9fc4-b61bcd9156cc
-- title:
--   Every index preceding the ceiling-grid terminal index occurs strictly before the horizon
-- statement:
--   For a strictly positive NNReal mesh h and finite terminal time T, each natural index j strictly below the ceiling of T/h has actual sampled physical time j*h strictly less than T. This is a deterministic bound enabling clipped terminal grids and unmodified earlier first passage samples.
-- source:
--   Pinned Mathlib Nat.lt_ceil, order preservation by multiplication with positive NNReal h, and division/multiplication cancellation.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped NNReal

theorem AvramDividend.Classical.chat03_ceiling_grid_preterminal_lt (T h : ℝ≥0) (hh : 0 < h) (j : ℕ)
    (hj : j < Nat.ceil (T / h)) :
    (j : ℝ≥0) * h < T := by
  sorry
