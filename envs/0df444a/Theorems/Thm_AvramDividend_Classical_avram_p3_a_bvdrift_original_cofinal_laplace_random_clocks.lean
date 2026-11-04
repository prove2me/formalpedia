-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_random_clocks
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_random_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:53:12.551768+00:00
-- url     : https://prove2.me/theorems/e53e510e-8950-4745-bb10-a2f6d61a58e0
-- title:
--   Original bounded-variation Lévy drift and negative jumps at source random clocks
-- statement:
--   Under BV and the genuine original negative-jump Laplace identity on cofinal source horizons, the actual drift-minus-negative-marked-jump interval formula holds almost surely at any two sample-dependent time clocks S,U ordered almost everywhere. The proof simply specialises the already proven all-interval full-measure event; it makes no new measurability, stopping-time, compensator or Markov assumptions.
-- source:
--   Source theorem a2de9927 exact almost-sure original all-interval identity, specialised to S(ω),U(ω) on the same ω and intersected with the clock ordering a.e. event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Transfer the original BV drift-minus-marked-jump identity to arbitrary
sample-dependent clocks, preserving the original space and true jumps. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_random_clocks
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
