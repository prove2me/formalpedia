-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:17:54.518842+00:00
-- url     : https://prove2.me/theorems/5dfadcd5-40e0-4824-bc1d-15f9ad1dbbc4
-- title:
--   Original BV one-event all-clock strict-survival prepayment drift strip, valid at arbitrary random observations
-- statement:
--   For the actual spectrally negative BV Levy field and admissible nonnegative dividend path, on one P-full event every nonnegative real physical observation clock strictly before ruin has controlled pre-right-dividend reserve between zero and initial surplus plus original drift times the clock. The a.e. quantifier precedes all clocks and thus supports arbitrary random observation times without an invalid null-set interchange.
-- source:
--   Proved/public f6cc1059 original BV a.e. global all-time nonincreasing negative Levy residual, 716ba871 cumulative dividend nonnegative, and 03a69d71 strict pre-ruin nonnegative reserve. This is stronger than previously Proved fixed-S 11a76c2c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + (t : ℝ) * X.drift := by sorry
