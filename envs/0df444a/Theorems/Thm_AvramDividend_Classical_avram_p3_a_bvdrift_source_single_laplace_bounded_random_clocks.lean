-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_single_laplace_bounded_random_clocks
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_single_laplace_bounded_random_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:10:29.866198+00:00
-- url     : https://prove2.me/theorems/894346f0-f205-4087-90b8-42e16acd1db6
-- title:
--   Original BV exact negative-jump source clock budget from a single finite-horizon laplace condition
-- statement:
--   For the same original bounded-variation spectrally negative Levy process, assume only the exact source laplace finite-horizon residual identity at T. For any original sample-dependent clocks S≤U≤T almost everywhere, the true original path increment equals physical drift times clock increment minus the genuine intrinsic marked negative-jump mass on (S,U]. The statement needs no cofinal family, no standing assumption and no alternative process.
-- source:
--   Direct specialisation of remotely Proved finite-horizon source all-interval theorem 4677903e-2b74-40ac-9c50-a09f0192fbab to S(ω), U(ω), using the a.e. ordering and upper-bound clock events.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One finite-horizon actual-source BV Laplace or residual moment condition
transfers the full marked negative-jump budget to ordered random clocks. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_single_laplace_bounded_random_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)))
    (S U : Ω → ℝ≥0)
    (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω)
    (hUT : ∀ᵐ ω ∂P, U ω ≤ T) :
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
