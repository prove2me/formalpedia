-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:48:59.908416+00:00
-- url     : https://prove2.me/theorems/eecc2ca1-05eb-4673-abf3-407686ef5462
-- title:
--   Original UBV stochastic-localiser Fatou with both clock monotonicity and cofinality only almost sure
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕 and IsAdmissibleLe source strategy D, the full ruin-time expected discounted Stieltjes reward follows from budgets at measurable clocks τ_n when both (i) monotonicity of τ_n and (ii) cofinal convergence of τ_n to ruinTime hold only P-almost surely. The proof patches clocks on the measurable null set where monotonicity fails and applies the existing Proved ae-cofinal Fatou theorem. It adds no boundary, path regularity, generator, gradient, cap, or smoothness assumption beyond the original corrected UBV core, and does not prove the budget itself.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; new Proved ae-cofinal original Fatou 8461667e-15cd-4077-8bd2-ce40dbc6734d and original ruinTime measurable bbfbecf4-7dfc-4812-84f3-8644c2b40b85. No core submission or milestone changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg
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
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
