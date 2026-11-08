-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:35:24.493179+00:00
-- url     : https://prove2.me/theorems/c5c292c4-69f3-4473-a059-4cb3bd8860ea
-- title:
--   Exact original localised stopped reward is HJB-bounded at the zero clock
-- statement:
--   For the actual original zero-clock reward F defined with the post-right-payment physical terminal and exact full closed Stieltjes cash, if the local clock is zero then F is bounded by w(x). Retains the time-zero dividend atom and original secant condition without assuming zero right dividend.
-- source:
--   Apply the Proved original zero-clock Term+Cash pathwise budget to the exact F source, using its physical W/Cash/Term equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hF : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : σ ω = 0) : F ω ≤ w x := by sorry
