-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:04:40.643016+00:00
-- url     : https://prove2.me/theorems/b065e392-0094-4781-8898-80d9c9d2e4a0
-- title:
--   Original zero-jump top-cap masked strict stopped reward is integrable
-- statement:
--   On the actual zero-jump Gaussian Lévy process X, original dividend strategy D and bounded stopping clock sigma, the exact zero-clock masked sum of discounted prepayment w at sigma and the strict-before-sigma Stieltjes cash is integrable. The theorem discharges the entire L1 conjunct of the source-equivalent c63d897f reward budget, with unchanged temporal payment chronology.
-- source:
--   Direct synthesis of Proved fdff2585 prepayment terminal L1, Proved ed1a42d8 strict dividend cash L1 and Proved ca595620 zero-clock mask L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact prepayment terminal plus strictly earlier Stieltjes dividends
    remains L1 under the true positive-clock mask at an infinite spatial cap. -/

theorem AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
