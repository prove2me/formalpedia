-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_signed_physical_grid_vanishing_error_fatou_closure
-- name    : AvramDividend.Classical.avram_p3_grid3_original_signed_physical_grid_vanishing_error_fatou_closure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:13:35.368344+00:00
-- url     : https://prove2.me/theorems/6b91bdc7-16e4-4a01-b3e8-1752f98aeb8a
-- title:
--   Original stopped physical signed grid with vanishing contact error yields exact six-clause strict Fatou witnesses
-- statement:
--   Given original X,D deterministic cofinal strict-horizon cash grids with integrable signed residual of nonpositive expectation, a mean-vanishing positive physical contact error and the exact pathwise grid budget, derive the true strict expected reward bound using the public sweep14 bridge and then the exact canonical signed Fatou witness clauses using the public grid3 strict-mean certificate. This is explicitly conditional on the genuine physical signed-grid source hypotheses; it does not assert those are yet established.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_canonical_signed_fatou_of_strict_expected_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_signed_physical_grid_vanishing_error_fatou_closure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (hSpos : 0 < (S : ℝ))
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (R J Err : ℕ → Ω → ℝ)
    (hSigned : ∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
      (∫ ω, R n ω + J n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErrMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0))
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) ≤ w x + (R n ω + J n ω) + max (Err n ω) 0) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let T : ℝ := (S : ℝ)
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
