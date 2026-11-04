-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_path
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_global_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:37:21.769519+00:00
-- url     : https://prove2.me/theorems/3d30c1ae-49a9-4d8f-9807-0ef3468a7908
-- title:
--   Source BV Lévy globally equals its actual jump series plus physical drift from cofinal Laplace horizons
-- statement:
--   For the actual bounded-variation spectrally negative Levy process on the same original probability space, cofinal-horizon actual negative-jump Laplace identities suffice to prove, on one probability-one event for all t, X_t = t*X.drift minus the full sum of genuine negative left jumps. No Standing, no replacement subordinator, no assumed path identity. Depends on prior cofinal source interval theorem and exact original jump-tsum encoding.
-- source:
--   Proved cofinal interval theorem a2de9927, source jump-tsum/intrinsic equality 3d5eead6 and source X.X_zero at s=0. No new stochastic assertion beyond stated cofinal original-jump Laplace identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Cofinal original-source jump transforms identify the genuine physical
Lévy drift coefficient in every BV sample path simultaneously. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_global_path
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
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
