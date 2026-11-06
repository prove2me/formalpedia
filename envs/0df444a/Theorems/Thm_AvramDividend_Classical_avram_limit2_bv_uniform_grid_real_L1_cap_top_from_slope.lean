-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_uniform_grid_real_L1_cap_top_from_slope
-- name    : AvramDividend.Classical.avram_limit2_bv_uniform_grid_real_L1_cap_top_from_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:14:07.14997+00:00
-- url     : https://prove2.me/theorems/58a6142d-6323-4b3b-8f23-5a32aed4ff4a
-- title:
--   BV physical signed Fatou grids to real perpetual value without extra positivity assumption
-- statement:
--   The original positive-cap C1 continuity and derivative lower bound imply nonnegative w(x) for each nonnegative admissible capital x by the Proved avram_p3_bv_initial_value_nonnegative. That exact mathematical deduction discharges the additional real-envelope positivity premise in the signed-Fatou-grid to real-perpetual-L1, capped and unrestricted value bridge, giving a source-exact interface with the canonical BV HJB hypotheses.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_cap_source_grid_exact_real_cash
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_original_grid_to_cap_and_top_values
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_uniform_grid_real_L1_and_cap_top
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_uniform_grid_real_L1_cap_top_from_slope
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
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D = ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
