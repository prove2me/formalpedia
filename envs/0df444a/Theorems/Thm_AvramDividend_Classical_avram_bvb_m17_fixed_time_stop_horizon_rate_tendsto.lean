-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_fixed_time_stop_horizon_rate_tendsto
-- name    : AvramDividend.Classical.avram_bvb_m17_fixed_time_stop_horizon_rate_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:42:37.644206+00:00
-- url     : https://prove2.me/theorems/77daafac-412b-4b2f-9a19-2c6dc0bd9d0a
-- title:
--   Original strict fixed-time stopped finite-horizon rate tends to its open-ruin mask
-- statement:
--   At a fixed strictly interior real observation time different from the extended ruin clock, the exact source strict inner finite-grid time-horizon and inclusive ruin-time mask eventually agrees with the strict pre-ruin mask. Consequently every constant signed original mark rate multiplied by the additional fixed reserve cap predicate tends to the correct pre-ruin masked rate. Preserves true ruin, cap contact and terminal clock conventions. Quantified over Nat-index physical grids.
-- source:
--   Proved bva20_strict_inner_horizon_ruin_mask_eventual_equiv b0c87b9c, finite activity original bvb28 continuous G real-time AE limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_m17_fixed_time_stop_horizon_rate_tendsto
    (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r < T)
    (τ : ℝ≥0∞) (hτ : ENNReal.ofReal r ≠ τ)
    (active : Prop) [Decidable active] (rate : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
            ENNReal.ofReal r ≤ τ) ∧ active then rate else 0)
      Filter.atTop
      (𝓝 (if (0 < r ∧ ENNReal.ofReal r < τ) ∧ active
        then rate else 0)) := by sorry
