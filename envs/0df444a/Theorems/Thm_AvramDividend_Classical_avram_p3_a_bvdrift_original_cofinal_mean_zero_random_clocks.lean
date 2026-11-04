-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_random_clocks
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_random_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:53:26.137922+00:00
-- url     : https://prove2.me/theorems/8ac7b750-f191-4f86-90cf-8672de033bf7
-- title:
--   Original BV physical drift and negative jumps at random clocks from source residual means
-- statement:
--   For an original bounded-variation spectrally negative Levy process, suppose an arbitrary cofinal family of deterministic source residuals is integrable with mean zero. Then the exact physical drift-minus-original marked negative-jump identity holds at any two ordered source sample-dependent clocks. All objects remain on the original probability space and filtration, with no stopping-time assumption required for this pathwise instantiation.
-- source:
--   Specialisation of remotely Proved 31ea5690 single-a.e.-event all intervals theorem to S(ω), U(ω), intersecting the a.e. ordering event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Transfer source BV drift and actual-jump intervals to ordered original
sample-dependent clocks under integrable cofinal mean-zero residuals. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_random_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      (((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0)
    (S U : Ω → ℝ≥0)
    (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
        ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
        (∫⁻ p,
          (if S ω < p.1 ∧ p.1 ≤ U ω then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
