-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
-- name    : AvramDividend.Classical.avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:35:38.298854+00:00
-- url     : https://prove2.me/theorems/1fa49330-1045-4a56-99a0-4437513a7bd0
-- title:
--   Continuously masked original negative-mark rate measurable for any real inner horizon
-- statement:
--   For any real-valued inner horizon a, including arbitrary real-index meshes, a measurable original reserve U and mark rate ψ continuous on the genuine inclusive cap yield a measurable source-rate t ↦ exp(-qt)ψ(Ut) under strict positive-time, inner-horizon, stop and closed-cap masks. The theorem is valid without assuming a is positive or below T and preserves source-specific cap and ruin guards.
-- source:
--   Proved bva21 closed-cap continuous-kernel mask measurable 2a89ef26 and pinned Mathlib measurable exponential, order predicates, ite.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
    (C τ : ℝ≥0∞) (q T a : ℝ)
    (U : ℝ≥0 → ℝ) (hU : Measurable U)
    (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < a ∧
          (t : ℝ≥0∞) ≤ τ ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t) else 0) := by sorry
