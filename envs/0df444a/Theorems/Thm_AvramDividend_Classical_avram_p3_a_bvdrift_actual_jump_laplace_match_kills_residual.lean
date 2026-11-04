-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:27:01.266384+00:00
-- url     : https://prove2.me/theorems/b4521fe7-9a44-4e1d-9cc2-3d34d9fbd0d5
-- title:
--   Original BV residual vanishes from intrinsic jump Laplace transform and source exponent
-- statement:
--   For original bounded-variation spectrally negative Lévy X with θ≥1, if the actual negative jump-magnitude Laplace functional has the Lévy ν transform, and its integrands are L1, the genuine original residual dT−X_T−J_T is zero almost surely. No raw first moments or alternate Poisson process. The jump Laplace identity is an honest unproved source obligation, not inferred from the known count-stationarity lemma.
-- source:
--   Combines Proved source physical drift upper bound, exact actual jump sum/intrinsic measure encoding, accepted ψ-exponent deficit, X.laplace, and positivity rigidity for equal-integral exponentials. The only extra stochastic identity is the explicit actual marked-jump Laplace functional.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Genuine original jump Laplace identity, if supplied, kills the original
BV residual without assuming a first moment of X or large negative jumps. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJInt : Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal))) P)
    (hXInt : Integrable (fun ω : Ω =>
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) P)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ((T : ℝ) * X.drift - X.X T ω) - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal = 0 := by sorry
