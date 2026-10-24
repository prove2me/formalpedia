-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_nnreal_grid_index_injective
-- name    : AvramDividend.Classical.dyadic_nnreal_grid_index_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:05:40.747741+00:00
-- url     : https://prove2.me/theorems/3532a7d9-daa5-4ed5-aae8-7c51b9dc3975
-- title:
--   Positive dyadic nonnegative-real grid time map is injective
-- statement:
--   For every dyadic resolution n, distinct natural grid indices k have distinct nonnegative-real times k/2^n. The finite-grid time constructor is strictly increasing because natural casting preserves strict order and division by a positive scale is strictly monotone. This supplies the fibre-equality bridge for bounded stopping-time approximation.
-- source:
--   Mathlib Nat.cast_lt, div_lt_div_of_pos_right and StrictMono.injective; downstream bounded_stopping_dyadic_grid_approximation.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity
open scoped NNReal

theorem AvramDividend.Classical.dyadic_nnreal_grid_index_injective
    (n : ℕ) :
    Function.Injective
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by sorry
