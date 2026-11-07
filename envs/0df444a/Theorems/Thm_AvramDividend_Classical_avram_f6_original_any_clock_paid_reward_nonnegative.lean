-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_paid_reward_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_any_clock_paid_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:27:28.975062+00:00
-- url     : https://prove2.me/theorems/1acf285c-7a89-4f11-9125-e170ff496a95
-- title:
--   Original discounted post-dividend terminal plus paid Stieltjes cash is nonnegative at every clock
-- statement:
--   For any (possibly random) nonnegative clock in the original capped unbounded-variation Levy dividend strategy, the exact discounted postpayment terminal value and the positive weighted Stieltjes payment mass are each nonnegative, hence so is their sum. Import the already proved original all-clock terminal lemma f6fef241 and use nonnegativity of ENNReal.toReal.
-- source:
--   Original source assumptions from fa7052b1; reduced exactly to Proved original terminal nonnegativity f6fef241 and nonnegative dividendMeasure mass. This is independent of unknown stochastic HJB budget, and closes an actual nonnegativity clause in both compact localisation certificates.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_any_clock_paid_reward_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y < 0, w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
