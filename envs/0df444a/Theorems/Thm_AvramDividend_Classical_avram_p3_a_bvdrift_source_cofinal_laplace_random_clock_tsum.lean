-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_cofinal_laplace_random_clock_tsum
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_cofinal_laplace_random_clock_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:19.948611+00:00
-- url     : https://prove2.me/theorems/241d7ef9-7e64-4cef-b427-a1a2b99f5f78
-- title:
--   Original BV drift and exact negative left-jump series at any sample-dependent clock under source Laplace identity
-- statement:
--   For the original spectrally negative BV Levy process, the true physical drift minus the source's full negative left-jump magnitude series holds almost surely at any original sample-dependent time clock U. This is a direct pathwise transfer of Proved 3d30c1ae-49a9-4d8f-9807-0ef3468a7908 and retains its explicit laplace assumptions. It does not introduce an alternative process, expected compensator or representation axiom.
-- source:
--   Exact source-a.e. all-time path theorem 3d30c1ae-49a9-4d8f-9807-0ef3468a7908 specialised at t=U(ω), retaining original Ω/P/filtration/left-jump series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_path

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV drift-minus-real-jump series at an arbitrary sample-dependent
clock, inherited from the source all-horizon almost-sure event. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_cofinal_laplace_random_clock_tsum
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
    (U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω = (U ω : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
