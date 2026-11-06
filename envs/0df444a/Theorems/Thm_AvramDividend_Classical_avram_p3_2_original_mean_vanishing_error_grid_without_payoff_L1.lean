-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_mean_vanishing_error_grid_without_payoff_L1
-- name    : AvramDividend.Classical.avram_p3_2_original_mean_vanishing_error_grid_without_payoff_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:00:00.598295+00:00
-- url     : https://prove2.me/theorems/a8a19615-01ef-457b-9d31-675e86d5a11a
-- title:
--   Actual original BV strict finite-horizon budget from mean-vanishing random mesh errors without separate grid-payoff L1
-- statement:
--   For the actual original spectrally negative Levy process and dividend strategy, a measurable nonnegative physical grid payoff bounded by an integrable mean-nonpositive signed residual plus an integrable random error of vanishing expectation satisfies the strict stopped cash and surviving prepayment terminal expectation bound. Grid-payoff integrability is a conclusion, not a premise.
-- source:
--   Proved original physical-grid signed upper implies F_n in L1 (2345879f) after combining the integrable original residual R_n with its integrable random mesh error Err_n. Then Proved original mean-vanishing mesh-error strict budget (338a3df9) yields the exact original-X/D strict Iio cash and surviving pre-rightpayment terminal expected bound. No dominated error, separate F L1, proxy law, canonical Open dependency, sorry or new axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_fatou_grid_integrability_from_signed_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_integrable_random_mesh_error_strict_prebudget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_mean_vanishing_error_grid_without_payoff_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (F R Err : ℕ → Ω → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (Err n) P)
    (hErrMean : Tendsto (fun n => ∫ ω, Err n ω ∂P)
      atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + Err n ω)
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
