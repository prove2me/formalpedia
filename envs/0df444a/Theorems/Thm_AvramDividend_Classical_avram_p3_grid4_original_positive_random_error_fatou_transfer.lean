-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_random_error_fatou_transfer
-- name    : AvramDividend.Classical.avram_p3_grid4_original_positive_random_error_fatou_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:24:59.709206+00:00
-- url     : https://prove2.me/theorems/6f4fc46b-7413-49c8-bda6-bd114a4bbdfb
-- title:
--   Original BV strict stopped cash and surviving terminal transfer vanishing physical-grid errors to exact signed Fatou
-- statement:
--   For the actual bounded-variation spectrally negative Levy process X and original dividend strategy D, the literal pre-rightpayment horizon terminal and strict stopped dividendMeasure cash prefix can be normalised to the exact six-clause signed Fatou certificate at positive w(x), provided authentic integrable compensated/HJB signed sources and an explicit physical-grid error with vanishing expected positive part satisfy the stated real pathwise inequality. It uses X.isProbability, the Proved original prefix Fatou theorem, and the separate proved random error centring lemma. The missing source comparison remains an explicit independent hypothesis, never hidden.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_random_positive_source_error_fatou_normalisation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_positive_random_error_fatou_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hwpos : 0 < w x)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T) (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (M B Err : ℕ → Ω → ℝ)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErrMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0))
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ w x + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
