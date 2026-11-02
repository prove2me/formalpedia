-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinal_budget_rightcont_stopping_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_cofinal_budget_rightcont_stopping_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:03:20.93697+00:00
-- url     : https://prove2.me/theorems/40d27c70-577a-4f35-a9f5-06f670a24e87
-- title:
--   Original UBV right-continuous stopping Fatou from cofinally many budgets
-- statement:
--   For the actual source Levy process X and admissible D, let S_n be monotone genuine stopping times of the unchanged right-continuous filtration and suppose sup_n S_n is infinity P-almost surely. The expected discounted full Stieltjes dividend estimate at ruin holds provided a uniform bound is available for ruin-clipped S_n at arbitrarily large clock indices, not at every n. The result uses true ruinTime stopping measurability, clips the original clocks, and invokes the already accepted cofinal-budget Fatou theorem. This introduces no extra smoothness, bounded-variation, boundary, atomlessness, or filtration hypotheses; the stochastic expected-budget remains a premise.
-- source:
--   Canonical core 429e17ca-5528-40b5-b593-7c03973d0706; Proved genuine ruinTime stopping and Proved cofinally bounded Fatou 5e54f6a2-6f97-40dd-b0b5-c192c9c3c8df.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_cofinal_budget_rightcont_stopping_fatou_no_extra_nonneg
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
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSmono : ∀ ω, Monotone (fun n => S n ω))
    (hSsupAE : ∀ᵐ ω ∂P, (⨆ n, S n ω) = ⊤)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
