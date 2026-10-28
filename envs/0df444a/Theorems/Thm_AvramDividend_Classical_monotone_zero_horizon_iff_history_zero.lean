-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_zero_horizon_iff_history_zero
-- name    : AvramDividend.Classical.monotone_zero_horizon_iff_history_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:46:20.340848+00:00
-- url     : https://prove2.me/theorems/4863715b-0fc8-427d-888c-fab34ec65157
-- title:
--   Zero at the horizon characterises a monotone path that has stayed at zero
-- statement:
--   For any nondecreasing real-valued path indexed by nonnegative real time and starting at zero, Y_t=0 is equivalent to Y_s=0 for all 0≤s≤t. This is the deterministic bridge from an actual Lévy residual zero-atom probability to the genuine no-residual-through-horizon survival probability.
-- source:
--   Elementary monotone path lemma for the finite-activity Lévy first-jump programme.

import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Monotone.Basic

open Set
open scoped NNReal

theorem AvramDividend.Classical.monotone_zero_horizon_iff_history_zero
    (Y : ℝ≥0 → ℝ) (hMono : Monotone Y)
    (hZero : Y 0 = 0) (t : ℝ≥0) :
    Y t = 0 ↔ ∀ s : ℝ≥0, s ≤ t → Y s = 0 := by sorry
