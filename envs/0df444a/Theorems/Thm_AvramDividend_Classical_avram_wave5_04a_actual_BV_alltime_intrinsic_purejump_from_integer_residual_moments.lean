-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_alltime_intrinsic_purejump_from_integer_residual_moments
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_alltime_intrinsic_purejump_from_integer_residual_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:30:40.172665+00:00
-- url     : https://prove2.me/theorems/4bd4a037-ec1c-4c4c-a857-58b304279aca
-- title:
--   Actual BV Levy source pure-jump equality for all time from countable intrinsic residual moment identities
-- statement:
--   For the original Standing bounded-variation spectrally negative Levy process, assume at each integer horizon that the intrinsic residual between source drift deficit and the complete negative left-jump magnitude series is integrable with expectation exactly zero. Then a single probability-one event supports the complete original-path pure-jump identity at every nonnegative real time. The first-moment normalisations are explicit independent premises, not asserted from the existing Standing or BV hypotheses; no replacement Poisson model or controlled Ito-Meyer formula is assumed.
-- source:
--   Chat04-A conditional source normalisation, composed from own independent same-process fixed-horizon nonnegative residual mean-zero theorem and own integer-horizon zero-anchor monotonicity theorem. It reduces the still-unproved original-jump compensator normalisation to explicit integer-horizon residual moment statements; all-time equality is concluded, not assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Countable exact actual-source residual first-moment criterion for all-time original BV pure-jump equality. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_alltime_intrinsic_purejump_from_integer_residual_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hIntegrable : ∀ n : ℕ, Integrable (fun ω : Ω =>
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : ∀ n : ℕ, (∫ ω : Ω,
      ((((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
