-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:16:52.77505+00:00
-- url     : https://prove2.me/theorems/b9ebb78a-05d4-4c9f-bd45-a282cc7e8ff4
-- title:
--   Actual BV source residual vanishes at a fixed horizon from its integrable nonnegative mean-zero identity
-- statement:
--   For the genuine original Standing bounded-variation spectrally negative Levy source, the residual drift deficit after all intrinsic negative left jumps is nonnegative almost surely. At a fixed physical time t, if this explicit actual-source residual is integrable and has expectation zero, it must vanish almost surely. Consequently X_t equals t times the original drift minus the exact intrinsic negative-jump magnitude integral at that horizon. The theorem is conditional on the stated first-moment identity; it does not assume the desired pure-jump equality, assert compensator existence, or replace the original source by an independent Poisson model.
-- source:
--   Original BV source moment-normalisation bridge. Uses canonical Proved zero-anchored residual 93ee4a8c-bc51-4b92-ad77-e9fcff70bbd6, which establishes the nonnegative residual for genuine original sample paths, and pinned Mathlib MeasureTheory.integral_eq_zero_iff_of_nonneg_ae, whose exact type was confirmed by the remote signature compiler. The hard original intrinsic compensator/moment equality remains an explicit unproved premise; this theorem formalises its exact consequence without assuming the full Ito-Meyer integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact fixed-time original BV residual mean-zero implies physical pure-jump equality, conditionally on the still missing moment calculation. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P,
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
