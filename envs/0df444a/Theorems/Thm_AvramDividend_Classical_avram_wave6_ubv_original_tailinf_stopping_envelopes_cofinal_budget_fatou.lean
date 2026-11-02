-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_tailinf_stopping_envelopes_cofinal_budget_fatou
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_tailinf_stopping_envelopes_cofinal_budget_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:45:23.051537+00:00
-- url     : https://prove2.me/theorems/f1ce155e-14de-49ac-b481-9ee152f260db
-- title:
--   Original UBV ruin Fatou for genuine monotone tail-inf stopping envelopes with cofinal budgets
-- statement:
--   For the original source spectrally negative Lévy process and admissible dividend strategy, form the tail infimum of all later genuine 𝓕.rightCont stopping clocks, clipped at actual ruin. These envelopes are themselves genuine right-continuous stopping times, monotone in n, and converge to actual ruin P-almost surely even when S_n are completely nonmonotone and have liminf infinity. It suffices that the expected discounted complete Stieltjes dividend bound holds at arbitrarily large envelope indices. Apply the Proved source stopping-envelope measurability/monotonicity, ruin-clipped liminf identity, and cofinally budgeted stochastic Fatou theorem. No extra boundary, filtration, smoothness or bounded-variation assumption.
-- source:
--   Accepted tail-inf original stopping theorem dae08fbd-1984-4610-8a6c-4d6acc3e1a75; source ruin liminf b6f6314c-f08c-4ac7-987f-77eeccb7e5fd; cofinal stochastic Fatou 5e54f6a2-6f97-40dd-b0b5-c192c9c3c8df.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_tailinf_stopping_envelopes_cofinal_budget_fatou
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
          (⨅ j : ℕ, min (ruinTime X x D ω) (S (n + j) ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
