-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_two_scale_original_strict_expected_budget
-- name    : AvramDividend.Classical.avram_bv_strict6_two_scale_original_strict_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:22:07.280017+00:00
-- url     : https://prove2.me/theorems/78dcdf14-f0cb-44d2-9376-b41e39b728ef
-- title:
--   Original BV strict expected source bound from cofinal clocks and two-scale physical grids
-- statement:
--   For the genuine original spectrally negative BV Levy reserve X and dividend D, assume each cofinal clock has integrable nonpositive-mean signed jump/HJB source on every physical refinement, nonnegative integrable source discrepancy with row-wise vanishing mean, and the literal strict pre-ruin paymentTimes intersection Iio cash plus surviving physical riskProcess terminal bounded by those sources. Choose one physical refinement per cofinal clock and apply the already Proved strict expected-budget transfer. This reduces two-scale expected source bounds to the true strict-horizon expectation, without asserting the remaining original physical source inequalities.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_nonnegative_error_mean
open Filter MeasureTheory Set AvramDividend.Classical
open scoped Topology NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_two_scale_original_strict_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (M B Err : ℕ → ℕ → Ω → ℝ) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    ∀ (hSigned : ∀ k n, Integrable (fun ω => M k n ω + B k n ω) P ∧
        (∫ ω, M k n ω + B k n ω ∂P) ≤ 0)
      (hErrInt : ∀ k n, Integrable (fun ω => max (Err k n ω) 0) P)
      (hErrMean : ∀ k, Tendsto
        (fun n => ∫ ω, max (Err k n ω) 0 ∂P) atTop (𝓝 0))
      (hPhysical : ∀ k n, ∀ᵐ ω ∂P,
        Cash (u k) ω + Term ω ≤
          w x + (M k n ω + B k n ω) + max (Err k n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x  := by sorry
