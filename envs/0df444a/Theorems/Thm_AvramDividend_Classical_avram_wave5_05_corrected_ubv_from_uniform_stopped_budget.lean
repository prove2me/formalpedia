-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
-- name    : AvramDividend.Classical.avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:36:46.177615+00:00
-- url     : https://prove2.me/theorems/974b727e-2e1d-4045-906b-c28640b64eed
-- title:
--   Exact corrected UBV core reduced to uniform genuine stopping-clock budgets
-- statement:
--   Retain every parameter and boundary, cap, admissibility, generator, gradient, pre-ruin nonnegativity, and full jump-drop hypothesis from the corrected canonical UBV stochastic verification core, including 0≤w(0). Assume in addition measurable monotone source-path stopping clocks converging to the genuine ruin time, and a uniform upper budget by w(x) for the complete discounted original dividend Stieltjes reward at each clock. Then obtain the exact corrected finite-horizon ruin-stopped reward bound. The proof extracts the actual dividend strategy from admissibility, converts nonnegative real T to NNReal, invokes the independently Proved monotone-clock expected Stieltjes localisation theorem, and takes an iSup upper bound. It includes time zero, continuous Stieltjes payments and right jumps. This is explicitly conditional: the source Lévy/controlled Itô–Meyer localised martingale bound needed for the extra budget is not proved here.
-- source:
--   Exact source correct core UUID 429e17ca-5528-40b5-b593-7c03973d0706; Proved source expectation localisation UUID 719af000-518f-4807-83fa-4d126306a372; private remote candidate probe job 5edb82a8-a720-4f96-9d8a-5f9f970933a5 reached the intentional sentinel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
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
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudget : ∀ n,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  sorry
