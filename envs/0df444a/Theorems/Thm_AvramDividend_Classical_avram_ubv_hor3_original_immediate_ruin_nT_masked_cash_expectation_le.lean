-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_nT_masked_cash_expectation_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_nT_masked_cash_expectation_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:24:38.206924+00:00
-- url     : https://prove2.me/theorems/17474c7b-dfac-49cf-89b0-7f68fa13a4e3
-- title:
--   Original true immediate-ruin finite clipped clock masked payout expectation bound including n zero
-- statement:
--   The original controlled spectrally negative Lévy process and original admissible dividends satisfy a masked expectation bound for the exact raw dividendMeasure payout on every sample path with ruinTime zero, for any natural clip n including n=0 and any nonnegative terminal horizon, with the full time-zero atom. This follows by integrating a genuine samplewise source HJB bound and has no auxiliary stopping, Cash, Term or martingale witness.
-- source:
--   Proved original samplewise n,T immediate ruin Stieltjes bound 8c661bc1; apply ENNReal lintegral_mono, split the true ruinTime zero event, and preserve original horizon right-payment atom. Requires 8c661bc1 to be Proved/public before submission.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_nT_stieltjes_pointwise_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_nT_masked_cash_expectation_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, if ruinTime X x D ω = 0 then
      (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if ruinTime X x D ω = 0 then
      ENNReal.ofReal (w x) else 0 ∂P) := by sorry
