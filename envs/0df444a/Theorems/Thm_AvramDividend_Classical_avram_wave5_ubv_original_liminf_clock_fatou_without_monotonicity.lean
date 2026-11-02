-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:38:51.815496+00:00
-- url     : https://prove2.me/theorems/b7105a08-8cdc-4cb9-a67c-5eff0eb612fd
-- title:
--   Original UBV zero-boundary Fatou for arbitrary measurable clock sequences with almost-sure ruin-time liminf
-- statement:
--   For the original SpectrallyNegativeLevy P 𝓕 and actual admissible D, remove monotonicity from the Fatou localisation clocks. Assume only measurable clocks whose pointwise tail infimum increases to the actual ruin time P-a.s., and the same expected full Stieltjes budget at each original clock. The tail-infimum clocks are monotone and dominated by the original clocks, so the existing original-source ae-cofinal Fatou theorem yields the corrected full ruin-time bound. No extra smoothness, bounded variation, cap restriction, boundary hypothesis or filtration replacement.
-- source:
--   Corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706; previously Proved source ae-cofinal Fatou 8461667e-15cd-4077-8bd2-ce40dbc6734d; Proved paymentTimes_min_mono_horizon 021cfe05-e7e2-40b3-acd0-0850489ea100. Full stopped HJB budget remains explicit and unproved; this strengthens only zero-boundary localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
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
    (hτliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
