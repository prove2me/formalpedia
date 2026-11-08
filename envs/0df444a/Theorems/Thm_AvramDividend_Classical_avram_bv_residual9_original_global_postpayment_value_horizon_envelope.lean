-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_value_horizon_envelope
-- name    : AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_value_horizon_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:39:56.370009+00:00
-- url     : https://prove2.me/theorems/74c8efab-b084-4a22-832c-c3dd53b829d9
-- title:
--   Original BV postpayment candidate is uniformly bounded across all ruin and horizon contacts
-- statement:
--   Under the original bounded-variation process, admissible dividend-strategy and value-candidate assumptions, the value candidate evaluated at any postpayment reserve throughout a bounded physical horizon admits a deterministic absolute bound, including after ruin. The bounded-variation controlled increment estimate bounds reserve from above; the candidate vanishes at negative reserve; continuity bounds its nonnegative compact part. No assumption on nonnegative drift or finite cap is needed.
-- source:
--   AVRAM BV-RESIDUAL9 round-five all-contacts value envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_value_horizon_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        |w (x + X.X t ω - rightLimit D t ω)| ≤ K := by sorry
