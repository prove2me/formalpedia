-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_strict_masked_reward_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss_top14_original_strict_masked_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:02:38.027195+00:00
-- url     : https://prove2.me/theorems/d9020a5d-8fc9-4a21-87ed-9cc9e3daba6b
-- title:
--   Original zero-jump top-cap masked strict reward is integrable at bounded true stops
-- statement:
--   For every bounded original right-continuous stopping clock, the zero-clock-masked strict prepayment reward is L1. Combine the Proved original top-cap prepayment terminal L1 result with the Proved strict-Iio cash envelope and measurable zero-clock mask. This proves the L1 conjunct of c63d897f without asserting its still-missing Gaussian expected HJB upper bound.
-- source:
--   Exact L1 conjunct of c63d897f-ed1b-465f-a542-bcc39fa65ca5, using Proved fdff2585 and e0aebc07; bridge requires hσle and hτeq to bound every σk by n.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss_top14_original_strict_masked_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ k ω, σ k ω ≤ T) :
    ∀ k, Integrable (fun ω =>
      if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
