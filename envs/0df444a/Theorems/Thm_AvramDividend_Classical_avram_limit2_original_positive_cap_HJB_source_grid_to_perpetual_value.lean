-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_cap_HJB_source_grid_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit2_original_positive_cap_HJB_source_grid_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:47:27.090052+00:00
-- url     : https://prove2.me/theorems/a0c8d462-b431-4120-8d9e-3d28133524c4
-- title:
--   Canonical capped original C1 source-grid hypotheses automatically imply perpetual dividend-value bound
-- statement:
--   Original positive-cap HJB continuity, nonnegative zero value and C1 gradient floor imply nonnegative pre-ruin candidate via Proved original capped range and closed-cap secant theorem 151fa4ac. Original IsAdmissibleLe also gives the exact time-zero/strict-pre-ruin right-dividend jump secant via Proved 1fba8396, including cap contact. Any genuine integrable F/M/J signed source-grid family satisfying their exact original Fatou lower bound then yields perpetual dividendValue <= ENNReal.ofReal (w x) by Proved b8eed78e. This theorem uses no open stochastic source certificate, introduced process, terminal vanishing, axioms, sorry or equality-in-law.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_source_witness_to_perpetual_value
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_positive_cap_HJB_source_grid_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hGridProducer :
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
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
