-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_laplace_global_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:10:37.607206+00:00
-- url     : https://prove2.me/theorems/b9efe711-9f1d-4e64-bd1d-e08d7120bad2
-- title:
--   Global all-interval original BV drift decomposition from integer-horizon source jump Laplace identities
-- statement:
--   For the same original bounded-variation spectrally negative Lévy process with no Standing condition, if the exact actual-negative-left-jump Laplace functional holds at every integer horizon n for one θ≥1, then there is one full-measure set of sample paths on which X_t−X_s=(t−s) X.drift minus the intrinsic original source negative-jump total on (s,t], for every s≤t. Automatic exponential integrability was separately proved; no alternative Poisson process, drift representation, or first moment is introduced.
-- source:
--   For each natural n use Proved 4677903e all subintervals of [0,n]. Take countable intersection by ae_all_iff and choose n≥t by exists_nat_ge, exactly as in Proved source d4b663c9, with no Standing assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Integer-horizon source Laplace identities give one probability-one
event supporting the exact original physical BV decomposition at all times. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_laplace_global_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hLap : ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-(((n : ℝ≥0) : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)))) :
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
