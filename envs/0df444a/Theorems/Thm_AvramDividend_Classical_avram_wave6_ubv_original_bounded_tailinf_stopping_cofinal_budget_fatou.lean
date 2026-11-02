-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_bounded_tailinf_stopping_cofinal_budget_fatou
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_bounded_tailinf_stopping_cofinal_budget_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:02:52.527846+00:00
-- url     : https://prove2.me/theorems/e7268cec-3391-4d78-a352-2d589973e1e3
-- title:
--   Original UBV ruin Fatou from cofinally budgeted bounded right-continuous tail-infimum stopping clocks
-- statement:
--   For genuine nonmonotone original 𝓕.rightCont stopping clocks S_n whose liminf is infinity almost surely, construct ρ_n by taking the future tail infimum, clipping at actual ruin, then clipping at finite integer horizon n. The Proved source package makes every ρ_n a stopping time bounded by n, increasing and converging to actual ruin a.s. If full discounted complete Stieltjes dividend budgets hold at arbitrarily large bounded ρ_n indices, then the complete ruin-time expected dividend bound follows by accepted source cofinal stochastic Fatou. This keeps the original process, filtration and admissible D, 0≤w(0), and zero/infinite ruin endpoints without extra boundary regularity or bounded-variation assumptions. The stopped budget remains explicit and is not supplied by this theorem.
-- source:
--   Dependent on original bounded stopping localiser package AvramDividend.Classical.avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers and Proved cofinal source Fatou 5e54f6a2-6f97-40dd-b0b5-c192c9c3c8df.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_bounded_nonmonotone_tailinf_stopping_localisers
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_bounded_tailinf_stopping_cofinal_budget_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (⨅ j : ℕ, min (ruinTime X x D ω) (S (n + j) ω))
            (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
