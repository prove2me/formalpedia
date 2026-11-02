-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:52:26.767636+00:00
-- url     : https://prove2.me/theorems/5e54f6a2-6f97-40dd-b0b5-c192c9c3c8df
-- title:
--   Original UBV Fatou from cofinally many bounded expected budgets
-- statement:
--   For the actual spectrally negative Levy process and actual admissible dividend strategy, the full expected discounted ruin-time Stieltjes dividend inequality follows if a monotone measurable original-clock sequence converges to ruin almost surely and the uniform expected budget holds at arbitrarily large localiser indices, not necessarily at every index or all sufficiently large indices. Monotonicity of paymentTimes and of nonnegative outer/inner lintegrals extends a cofinal budget to each earlier index. The Proved original-source almost-sure cofinal Fatou theorem then applies. This retains the source filtration, UBV, w(0)≥0, terminal sign and unmodified smoothness/generator hypotheses. The stochastic budget at cofinally many bounded clocks is still a premise and does not replace the missing controlled Itô–Meyer argument.
-- source:
--   Canonical corrected core 429e17ca-5528-40b5-b593-7c03973d0706; Proved ae-cofinal Fatou 8461667e-15cd-4077-8bd2-ce40dbc6734d and monotone paymentTimes 021cfe05-e7e2-40b3-acd0-0850489ea100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsupAE : ∀ᵐ ω ∂P, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
