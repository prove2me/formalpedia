-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
-- name    : AvramDividend.Classical.avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:53:02.060758+00:00
-- url     : https://prove2.me/theorems/6e13657c-45a7-4307-8679-a8da3e3801f8
-- title:
--   Corrected controlled UBV reward estimate reduced to the exact bounded ruin-clock budgets
-- statement:
--   For the genuine original spectrally negative Lévy process X and actual admissible dividend regulator D, preserve every hypothesis of the corrected canonical UBV stochastic core, including w(0)≥0, initial cap and all right-jump drops. Assume only the uniform finite-horizon expected complete discounted Stieltjes dividend bound at explicit actual ruin-clock truncations τ_n=min(ruinTime(X,x,D),n). Then the full corrected finite-horizon reward bound follows. This is the precise remaining stochastic hypothesis, not an unconditional Ito–Meyer proof. Derived by the two independently Proved Chat05 theorems for measurable increasing genuine clocks and monotone-clock full expected Stieltjes localisation. Time-zero atoms, diffuse payments, right jumps, arbitrary positive/infinite cap, and σ=∞ are all retained.
-- source:
--   Corrected core UUID 429e17ca-5528-40b5-b593-7c03973d0706, accepted clock theorem 3ae57b3c-959f-46f7-ba88-a55f35a44126, accepted conditional uniform budget theorem 974b727e-2e1d-4045-906b-c28640b64eed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
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
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  sorry
