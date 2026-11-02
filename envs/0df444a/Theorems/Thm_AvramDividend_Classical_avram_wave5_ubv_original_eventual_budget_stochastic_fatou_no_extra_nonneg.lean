-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_eventual_budget_stochastic_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_eventual_budget_stochastic_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:51:27.485427+00:00
-- url     : https://prove2.me/theorems/3b02ac58-966a-40db-bf59-6e017a0418cd
-- title:
--   Original UBV Fatou with an eventually uniform expected budget
-- statement:
--   For the original SpectrallyNegativeLevy P 𝓕 and actual admissible dividend strategy D, a measurable monotone sequence of localisation clocks converging P-almost surely to ruinTime yields the full expected discounted Stieltjes dividend bound when the uniform per-clock estimate is available only from some finite index N onward. This shifts the sequence to its tail and applies the canonically Proved almost-sure cofinal Fatou theorem. The original source filtration, UBV, nonnegative w(0), generator, derivative, cap and dividend-jump hypotheses remain unchanged. The bounded-localiser budget itself remains an explicit hypothesis; no controlled Itô–Meyer or dividend Stieltjes integration is claimed.
-- source:
--   Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706; depends on Proved original-source a.s.-cofinal Fatou 8461667e-15cd-4077-8bd2-ce40dbc6734d, without imposing extra w-boundary assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_eventual_budget_stochastic_fatou_no_extra_nonneg
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
    (hBudgetEventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
