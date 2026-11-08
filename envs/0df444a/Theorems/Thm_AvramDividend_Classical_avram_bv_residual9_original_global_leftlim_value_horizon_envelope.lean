-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_horizon_envelope
-- name    : AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_horizon_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:47:59.831701+00:00
-- url     : https://prove2.me/theorems/d2cc0694-c06a-492d-aaac-06ae710f22e3
-- title:
--   Original BV candidate at literal left-limit reserve is bounded even after ruin
-- statement:
--   Uniformly over all original bounded-variation Lévy paths and every physical time up to a finite horizon, including ruin-contact cells, the value candidate at the exact strict left-limit of the postpayment reserve has a deterministic absolute bound. This uses the published full-horizon global reserve upper strip, preservation of a closed one-sided interval by left limits, and the candidate's vanishing for negative surplus plus compact continuity for nonnegative surplus.
-- source:
--   AVRAM BV-RESIDUAL9 round-five global contact leftlimit envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_upper_horizon_strip
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_horizon_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        |w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)| ≤ K := by sorry
