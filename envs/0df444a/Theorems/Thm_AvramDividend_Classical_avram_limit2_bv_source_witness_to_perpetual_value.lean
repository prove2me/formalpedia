-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_source_witness_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit2_bv_source_witness_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:39:57.499027+00:00
-- url     : https://prove2.me/theorems/b8eed78e-9ef0-4b90-87f3-e7a68f80b120
-- title:
--   Original BV source-grid witness family implies actual perpetual dividend value bound
-- statement:
--   For each strictly positive original stopped horizon, assume genuine nonnegative integrable finite-grid source payoffs, integrable signed compensation with nonpositive expectation, the pathwise source HJB budget, and a Fatou lower bound for the actual strict dividend cash plus the surviving prepayment terminal. The original-process strict terminal nonnegativity and already Proved probability-normalised limit lemma then establish the full dividendValue bound without terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_survival_preterminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_probability_real_grids_to_perpetual_value
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_source_witness_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hSource : ∀ (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T),
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
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
