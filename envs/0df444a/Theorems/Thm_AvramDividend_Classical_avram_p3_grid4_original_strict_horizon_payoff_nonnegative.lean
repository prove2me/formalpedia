-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_horizon_payoff_nonnegative
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_horizon_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:30.6611+00:00
-- url     : https://prove2.me/theorems/f1a445c6-9cc2-4fa5-9f29-ac58a0e338b1
-- title:
--   Original strict-horizon stopped discounted dividend cash plus surviving reserve reward is nonnegative
-- statement:
--   On the true original process X and original dividendMeasure D, the strict Iio T discounted cash has nonnegative ENNReal.toReal, and the surviving pre-rightpayment terminal w(riskProcess X x D S) is nonnegative at positive T by the actual pre-ruin positivity hypothesis. Hence their sum is nonnegative pathwise; no assumption of a finite horizon atom or synthetic process is made. A source-faithful positivity component for the localised Fatou grid and its original stopped reward.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_horizon_payoff_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (ω : Ω) :
    let S : ℝ≥0 := ⟨T, hT⟩
    0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
           ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
           Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) := by sorry
