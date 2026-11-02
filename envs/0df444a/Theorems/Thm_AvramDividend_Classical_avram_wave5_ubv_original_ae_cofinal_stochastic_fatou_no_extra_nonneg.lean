-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:24:30.694195+00:00
-- url     : https://prove2.me/theorems/8461667e-15cd-4077-8bd2-ce40dbc6734d
-- title:
--   Original UBV Fatou passage under almost-sure, rather than pathwise, cofinal stochastic localisation
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕 and actual admissible strategy D, under exactly the corrected UBV core assumptions except its redundant hw_nonneg binder, the full expected discounted ruin-time Stieltjes dividend estimate follows from uniform budgets at measurable monotone stochastic ruin-clock approximants τ_n provided sup_n τ_n equals the genuine ruin time P-almost surely. This weakens the previously Proved Fatou bridge's pathwise cofinality to the natural almost-sure form without any new boundary, regularity, jump, bounded variation, or cap conditions. Patch clocks on the measurable P-null failure set to equal ruinTime pointwise; the outer expected rewards are unchanged almost everywhere; then apply the already Proved full Stieltjes Fatou theorem. The uniform hBudget is still a hypothesis; no integration or martingale estimate is asserted.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; reuse Proved ruinTime measurability bbfbecf4-7dfc-4812-84f3-8644c2b40b85, source gradient nonnegative a81e26e3-b329-4cf1-bd1f-7ce8d83fd66b, full Fatou from stopped budget 974b727e-2e1d-4045-906b-c28640b64eed. Do not modify source/core or milestones.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
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
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
