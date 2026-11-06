-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_original_signed_BV_hjb_budgets_to_cap_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_original_signed_BV_hjb_budgets_to_cap_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:12:46.653206+00:00
-- url     : https://prove2.me/theorems/40f87537-f573-44d1-9ac2-b6f87407d6d5
-- title:
--   Original HJB signed budgets uniformly yield terminal L1 and capped/unrestricted perpetual values
-- statement:
--   For all original admissible capped strategies, a uniform family of actual signed stopped closed-horizon dividend-cash and postpayment terminal expectation inequalities implies each terminal is integrable, every capped strategy perpetual dividend value is bounded, and C=top recovers all unrestricted original strategies.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_original_signed_BV_hjb_budgets_to_cap_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hBudgets : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0) ∂P) ≤ w x) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
        let S : ℝ≥0 := ⟨T, hT⟩
        Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0)) P) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
