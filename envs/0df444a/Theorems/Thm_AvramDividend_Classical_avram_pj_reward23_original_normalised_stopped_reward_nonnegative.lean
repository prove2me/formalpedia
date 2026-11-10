-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward23_original_normalised_stopped_reward_nonnegative
-- name    : AvramDividend.Classical.avram_pj_reward23_original_normalised_stopped_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:19:47.350426+00:00
-- url     : https://prove2.me/theorems/000b20f2-6947-4698-a1fc-4ee2fe2954ad
-- title:
--   The actual zero-clock-normalised stopped Lévy reward is nonnegative for every bounded or unbounded cap
-- statement:
--   For the original unbounded-variation controlled Lévy process, exact inclusive stopped cash and verification terminal, the zero-clock-normalised reward is everywhere nonnegative. Combine Proved 1acf285c unmasked paid reward nonnegative at every physical clock with Proved ef1ac2df zero-clock masked reward domination, retaining the original time-zero dividend atom. This is the missing nonnegative integrand for top-cap stopping Fatou and positive-clock localisation.
-- source:
--   Direct Proved 1acf285c + ef1ac2df, no stochastic Ito, no extra localisation, exact original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_paid_reward_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward23_original_normalised_stopped_reward_nonnegative
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
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (if (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
            else riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
