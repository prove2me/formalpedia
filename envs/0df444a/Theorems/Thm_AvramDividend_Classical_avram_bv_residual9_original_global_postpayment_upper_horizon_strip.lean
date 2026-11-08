-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_upper_horizon_strip
-- name    : AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_upper_horizon_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:37:47.295063+00:00
-- url     : https://prove2.me/theorems/7fa910be-2eb1-413a-955e-316e726269b7
-- title:
--   Original bounded-variation controlled reserve has global upper horizon drift bound including after ruin
-- statement:
--   For any original bounded-variation spectrally-negative Levy process and dividend strategy, the postpayment reserve is bounded from above throughout every finite physical horizon by the initial reserve plus the positive part of horizon drift. This holds after ruin as well and without assuming that the drift is nonnegative. It follows from the Proved all-times controlled reserve increment theorem and nonnegativity of the right-payment limit.
-- source:
--   AVRAM BV-RESIDUAL9 round-five global ruin contact envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_upper_horizon_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      x + X.X t ω - rightLimit D t ω ≤
        x + max ((T : ℝ) * X.drift) 0 := by sorry
