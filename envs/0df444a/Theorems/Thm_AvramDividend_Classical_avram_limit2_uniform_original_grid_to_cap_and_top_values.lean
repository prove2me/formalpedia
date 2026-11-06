-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_original_grid_to_cap_and_top_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_original_grid_to_cap_and_top_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:46:20.573233+00:00
-- url     : https://prove2.me/theorems/982b6117-ed6d-4d2a-a688-7841d3ebf03a
-- title:
--   Uniform original source-grid certificates bound all capped and unrestricted perpetual dividends
-- statement:
--   A uniform family of true original compensated finite F/M/J strict pre-ruin cash and terminal signed Fatou source certificates, with actual time-zero and pre-ruin jump controls, bounds the perpetual value of every capped admissible strategy and at top cap every unrestricted strategy. Each strategy also has integrable real perpetual dividend cash by the accepted original-process source-grid theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_cap_source_grid_exact_real_cash
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_original_grid_to_cap_and_top_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hGridProducers : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) →
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))) →
      ∀ (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T),
      ∃ F M J : ℕ → Ω → ℝ,
        (∀ n, Measurable (F n)) ∧
        (∀ n, Integrable (F n) P) ∧
        (∀ n, 0 ≤ᵐ[P] F n) ∧
        (∀ n, Integrable (fun ω => M n ω + J n ω) P ∧
          (∫ ω, M n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n ω + J n ω)) ∧
        (∀ᵐ ω ∂P,
          let S : ℝ≥0 := ⟨T, hT⟩
          ENNReal.ofReal
            ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)).toReal +
              (if (S : ℝ≥0∞) < ruinTime X x D ω then
                Real.exp (-(q * T)) * w (riskProcess X x D S ω)
              else 0)) ≤
            liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
