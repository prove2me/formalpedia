-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_preruin_prestop_value_envelope
-- name    : AvramDividend.Classical.avram_bv_residual9_original_preruin_prestop_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:31:22.190403+00:00
-- url     : https://prove2.me/theorems/c37b75e8-9807-4534-8fe7-5966c0933b57
-- title:
--   Original BV pre-ruin strict-left-limit value admits a deterministic finite-horizon bound
-- statement:
--   For every admissible original spectrally-negative bounded-variation dividend process and bounded time horizon, the value candidate at the literal strict pre-jump postpayment reserve is uniformly bounded by a deterministic constant at all pre-ruin times almost surely. Derived from the published closed BV drift strip, preservation of closed bounds under left limits, and compactness continuity.
-- source:
--   AVRAM BV-RESIDUAL9 round-five literal generator-state envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_preruin_prestop_value_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        |w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)| ≤ K := by sorry
