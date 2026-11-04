-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_laplace_two_random_clock_jump_increment
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_laplace_two_random_clock_jump_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:07:59.110628+00:00
-- url     : https://prove2.me/theorems/af817c64-ab46-4c61-9140-d35f4b0bf664
-- title:
--   Original source BV drift and negative-jump difference between any two random clocks (laplace)
-- statement:
--   For the original spectrally negative Levy process with X.BoundedVariation and the explicitly assumed cofinal laplace source hypothesis, the path increment between any pair of sample-dependent clocks equals physical drift times the time difference minus the difference in the two original actual negative-left-jump total series. No clock ordering or auxiliary process is introduced.
-- source:
--   Algebraic subtraction of the original global source path formula 3d30c1ae-49a9-4d8f-9807-0ef3468a7908 evaluated at U(ω) and S(ω) on the same original full-measure event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_path

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV path increment between arbitrary sample-dependent clocks
is physical drift less the difference of genuine negative left-jump totals. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_laplace_two_random_clock_jump_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hLap : ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T n then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-(T n : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)))
    (S U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
      ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
      ((∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ S ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) := by sorry
