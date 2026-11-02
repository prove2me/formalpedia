-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_monotone_cofinal_budget_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_cofinal_budget_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:06:29.620772+00:00
-- url     : https://prove2.me/theorems/d68d6e46-0943-4eb2-8f8e-ae1fa27b1fa4
-- title:
--   Original UBV Fatou under a.s. monotone clocks and cofinally many budgets
-- statement:
--   In the original SpectrallyNegativeLevy P 𝓕 model with actual admissible D, both the monotonicity of measurable ruin-clock approximants and their convergence to ruin may hold merely P-almost surely. Furthermore, the uniform expected discounted Stieltjes dividend budget need only hold along an unbounded set of clock indices. For each earlier clock, use the almost-sure inclusion of paymentTimes and monotonicity of inner and outer nonnegative integrals to inherit a later bound. Apply the Proved a.s.-monotone, a.s.-cofinal Fatou theorem. This retains hw0≥0, exact generator/gradient/jump hypotheses and the original source filtration, adding no boundary or regularity assumptions. The stochastic budget is a premise.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; Proved ae-monotone Fatou eecc2ca1-05eb-4673-abf3-407686ef5462 and source paymentTimes inclusion 021cfe05-e7e2-40b3-acd0-0850489ea100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_cofinal_budget_fatou_no_extra_nonneg
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
    (hτmonoAE : ∀ᵐ ω ∂P, Monotone (fun n => τ n ω))
    (hτsupAE : ∀ᵐ ω ∂P, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
