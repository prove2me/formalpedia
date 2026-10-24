-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_eq_iff_time_cell
-- name    : AvramDividend.Classical.dyadic_ceiling_index_eq_iff_time_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:03:21.758765+00:00
-- url     : https://prove2.me/theorems/6217ec63-70c5-49e9-a2fd-659f91c671f0
-- title:
--   Positive dyadic ceiling index characterises a half-open stopping-time cell
-- statement:
--   For any nonnegative time t, dyadic scale 2^n and positive natural index k, ceiling(2^n t)=k exactly when (k−1)/2^n < t ≤ k/2^n. The precise half-open fibre characterisation is the filtration-measurability bridge needed to prove existence of finite-valued approximating stopping times.
-- source:
--   Mathlib Nat.ceil_eq_iff with positive power and field inequalities; downstream bounded_stopping_dyadic_grid_approximation.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_index_eq_iff_time_cell
    (t : ℝ≥0) (n k : ℕ) (hk : k ≠ 0) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) = k ↔
      ((k - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n < (t : ℝ) ∧
      (t : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ n := by sorry
