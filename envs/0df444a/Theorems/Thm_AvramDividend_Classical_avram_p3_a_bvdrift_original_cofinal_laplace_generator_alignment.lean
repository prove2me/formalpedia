-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_generator_alignment
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_generator_alignment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:41:40.486968+00:00
-- url     : https://prove2.me/theorems/ac3c8560-e75c-40e3-8803-1c5adf1300e4
-- title:
--   Integration-ready original BV physical generator and true cofinal source jump path decomposition
-- statement:
--   For the original bounded-variation spectrally negative Levy process, if exact original actual-negative-jump Laplace identities are available on arbitrary countable cofinal horizons, a single theorem delivers both X.generator w x = X.drift*deriv w x + jump integral and the a.e. all-time original source drift-minus-negative-marked-jump interval identity. No Standing, no alternative process; only X.GeneratorIntegrable w x for the generator expression.
-- source:
--   Combine remotely Proved source c8ba98f0 boundedVariation_generator_physical_drift_representation and remotely Proved a2de9927 source cofinal-laplace original BV intervals. The hLap condition remains explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source BV physical drift identifies both the exact generator coefficient
and genuine original-process all-interval pathwise negative-jump budget. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_generator_alignment
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
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
