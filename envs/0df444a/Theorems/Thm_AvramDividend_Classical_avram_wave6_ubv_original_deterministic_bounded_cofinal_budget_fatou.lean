-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_cofinal_budget_fatou
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_deterministic_bounded_cofinal_budget_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:59:31.536075+00:00
-- url     : https://prove2.me/theorems/2844248a-ff7b-4db5-9b1a-b3527db4f8a5
-- title:
--   Original UBV deterministic bounded ruin clocks, cofinally budgeted Fatou to ruin
-- statement:
--   For the actual original SpectrallyNegativeLevy P 𝓕 and admissible D, the corrected UBV full expected discounted Stieltjes ruin-time dividend estimate follows if its stopped expectation budget holds at arbitrarily large deterministic integer horizons min(ruinTime,n), rather than at every n. The actual bounded ruin-clock theorem gives measurable pointwise monotone clocks converging to ruinTime on every path, including zero and infinite ruin. Invoke the Proved cofinally budgeted stochastic Fatou theorem. The original source filtration, 0≤w(0), regularity, generator, gradient and dividend hypotheses are unchanged; the finite-clock stochastic expected budget remains an explicit premise, not an assertion of controlled Itô–Meyer.
-- source:
--   Proved original bounded ruin-clock theorem 3ae57b3c-959f-46f7-ba88-a55f35a44126; accepted cofinally budgeted original stochastic Fatou 5e54f6a2-6f97-40dd-b0b5-c192c9c3c8df; corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_cofinally_bounded_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_deterministic_bounded_cofinal_budget_fatou
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
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
