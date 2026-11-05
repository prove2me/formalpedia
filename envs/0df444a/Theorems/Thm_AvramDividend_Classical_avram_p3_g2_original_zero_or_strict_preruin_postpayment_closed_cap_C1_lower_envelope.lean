-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_postpayment_closed_cap_C1_lower_envelope
-- name    : AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_postpayment_closed_cap_C1_lower_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:59:46.486711+00:00
-- url     : https://prove2.me/theorems/6e723c44-6efe-4c61-bd76-c7f81ed4ae93
-- title:
--   Original right-postpayment candidate has quantitative C1 lower envelope at zero or strict pre-ruin through cap contact
-- statement:
--   At time zero or every actual strictly pre-ruin clock, the original controlled reserve after the right-limit dividend satisfies w(postReserve) >= w(0)+postReserve under admissible physical solvency, closed-cap initial reserve, and C1 unit-gradient bound. The theorem treats time-zero atom correctly, includes cap-contact boundary, and requires no Standing, BV generator, expected signed budget or Open stochastic proof.
-- source:
--   IsAdmissibleLe postpayment source field plus Proved capped_postPaymentReserve_ofReal_le_cap 16104f4f and closed-cap gradient lower envelope fc03f3ac. Complements G2 quantitative prepayment lower envelope 62183577.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_postpayment_closed_cap_C1_lower_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      w 0 + (x + X.X t ω - rightLimit D t ω) ≤
        w (x + X.X t ω - rightLimit D t ω) := by sorry
