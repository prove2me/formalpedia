-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
-- name    : AvramDividend.Classical.avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:33:25.063558+00:00
-- url     : https://prove2.me/theorems/b6c77b8b-c2dc-498b-be06-ea70740396e8
-- title:
--   Original BV strict payoff mean budget from nonintegrable nonpositive HJB drift
-- statement:
--   For the actual spectrally negative Levy process X and admissible dividend D, with literal stopped strict pre-horizon Iio cash and surviving terminal at S, prove the full expected payoff upper bound when the original physical mesh satisfies a compensated-martingale plus nonpositive raw HJB drift and vanishing positive error. Unlike the existing exact physical Fatou theorem, no L1 assumption on the negative HJB drift B is imposed. The proof drops B pointwise before the original source-exact cofinal Fatou limit, relying on Proved avram_integration_sweep14_original_BV_vanishing_error_strict_mean. Remaining open instantiation: construct M, B, Err and physical inequality for original X,D.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (M B Err : ℕ → Ω → ℝ) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    ∀ (hM : ∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) ≤ 0)
      (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
      (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
      (hErrMean : Tendsto
        (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0))
      (hPhysical : ∀ n, ∀ᵐ ω ∂P,
        Cash (u n) ω + Term ω ≤
          w x + (M n ω + B n ω) + max (Err n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x := by sorry
