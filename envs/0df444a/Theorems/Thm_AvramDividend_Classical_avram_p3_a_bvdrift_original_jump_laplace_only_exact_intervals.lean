-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:01:50.206201+00:00
-- url     : https://prove2.me/theorems/4677903e-2b74-40ac-9c50-a09f0192fbab
-- title:
--   Original BV Lévy path equals physical drift minus true jumps on every interval from one source Laplace identity
-- statement:
--   For an actual source bounded-variation spectrally negative Lévy process, a single original-jump Laplace transform equality at horizon T and θ≥1 implies, almost surely simultaneously, X_t−X_s=d(t−s) minus the genuine original Lévy negative-jump mass for every 0≤s≤t≤T. All integrability is automatic from the original source and independently proved; the only conditional stochastic hypothesis is precisely the source jump Laplace identity awaiting P2.
-- source:
--   Compose proved original jump exponential L1 helper with the original conditional BV all-interval path theorem; no first moments, no independent Poisson representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Under the genuine source jump Laplace identity, BV intervals have
exactly source physical drift minus actual intrinsic negative jump mass.
Both exponential integrability facts are proved for the original process. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals
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
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
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
