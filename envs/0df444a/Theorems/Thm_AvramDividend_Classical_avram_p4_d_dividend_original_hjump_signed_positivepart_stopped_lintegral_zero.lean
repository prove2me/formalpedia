-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:10:31.536432+00:00
-- url     : https://prove2.me/theorems/e98986a3-cb05-4acd-b0a8-c2e85130c247
-- title:
--   Original variable-size right-dividend hjump signed residual has zero positive-part integral on literal stopped Stieltjes reward
-- statement:
--   For the exact original paymentTimes(ruinTime) intersect closed finite horizon, the positive-part ENNReal lintegral against the full original dividendMeasure of the discounted actual variable-size right-dividend remainder is zero. On any true payment time t, the canonical explicit hjump applies to the post-original-Lévy-jump riskProcess U_t and rightLimit D t-D t. The pointwise signed remainder is nonpositive; the source measurable reward domain makes the restricted lintegral zero. Includes t=0 even immediate ruin, eligible horizon payment, simultaneous X and D jumps, singular continuous mass, and never requires integrability of the signed remainder.
-- source:
--   Exact canonical P4-F hjump source 0dda1be7; source-proved paymentTimes_measurable; copied measure set restriction and lintegral_congr_ae structure from public proved Wave5 c6c9ef5f, replacing the fixed positive forward δ with actual rightLimit D-D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual size-dependent, source-ordered right-dividend signed residual has zero
    positive-part lintegral on the exact ruin-stopped Stieltjes reward set. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
          w (riskProcess X x D s.toNNReal ω -
            (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
          w (riskProcess X x D s.toNNReal ω)))
        ∂(dividendMeasure D ω)) = 0 := by sorry
