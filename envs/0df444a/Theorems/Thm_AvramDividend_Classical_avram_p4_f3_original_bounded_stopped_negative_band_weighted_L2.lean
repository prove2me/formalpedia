-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_bounded_stopped_negative_band_weighted_L2
-- name    : AvramDividend.Classical.avram_p4_f3_original_bounded_stopped_negative_band_weighted_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:55:04.252213+00:00
-- url     : https://prove2.me/theorems/c4a7501e-d82b-40d9-91bc-65f4060a6af5
-- title:
--   Physical bounded-stop negative-band count with bounded random source weight has a certified L² energy budget
-- statement:
--   For the original spectrally negative Levy process X and any bounded sample-path stopping horizon tau with a measurable intrinsic negative-band jump count K, a measurable random real weight H of absolute value at most B preserves square integrability of the physical weighted count H*K. Its real squared expectation is bounded by B squared times the exact original finite-horizon count budget r squared plus r. This supplies a source-faithful quadratic domination for finite-grid stopped jump terms; it does not assert zero mean or predictability of H.
-- source:
--   Direct weighted L² consequence of Proved public P4-S3 original bounded stopped negative-band count square budget 50312326-0cf3-4631-aed2-a848ba3ce0a5, by measurable pointwise domination and Bochner integral monotonicity. Original X, original stopping clock and original intrinsic jump set are preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_bounded_stopped_negative_band_weighted_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard))
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (H ω * (K ω : ℝ)) ^ 2) P ∧
      (∫ ω, (H ω * (K ω : ℝ)) ^ 2 ∂P) ≤ B ^ 2 * (r ^ 2 + r) := by sorry
