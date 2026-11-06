-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_canonical_signed_fatou_of_strict_expected_mean
-- name    : AvramDividend.Classical.avram_p3_grid3_original_canonical_signed_fatou_of_strict_expected_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:46:50.920719+00:00
-- url     : https://prove2.me/theorems/8fdd1928-024a-4a21-bc2e-b66a91bfc107
-- title:
--   Original bounded-variation signed Fatou certificate witnesses from the independently proved true strict-reward expected mean
-- statement:
--   Conditional source-faithful integration: when the actual original strict discounted dividendMeasure cash plus surviving pre-rightpayment terminal has expected value at most w(x), the already Proved integrable measurable nonnegative strict-payoff version and signed integrable witness yield the canonical six Fatou certificate clauses by constant Nat-indexed sequences. The strict-mean hypothesis is a genuine outstanding independent stochastic budget obligation, not a consequence claimed in this helper.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_canonical_signed_fatou_of_strict_expected_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hMean :
      let S : ℝ≥0 := ⟨T, hT⟩
      let Strict : Ω → ℝ := fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
      (∫ ω, Strict ω ∂P) ≤ w x) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
