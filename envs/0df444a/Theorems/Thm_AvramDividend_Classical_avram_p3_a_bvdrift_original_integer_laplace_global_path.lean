-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_path
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_laplace_global_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:42.886466+00:00
-- url     : https://prove2.me/theorems/45236e85-809b-49cd-a37b-5e46bf684bde
-- title:
--   The genuine original BV Lévy path globally equals source physical drift minus all actual negative left jumps
-- statement:
--   For the original same-Ω/P/filtration BV spectrally negative Lévy process, assuming exact jump Laplace functional only at every natural horizon for a fixed θ≥1, there is one probability-one event on which X_t = X.drift*t − Σ_{0<s≤t}(leftLim X_s − X_s) for every t≥0. All jumps are the genuine source sample path. No Standing assumption, arbitrary separate process, finite mean or compensated-truncation assumption. The original characteristic convention's drift has already been matched to X.generator.
-- source:
--   Proved full all-interval original BV path from integer-horizon Laplace plus Proved exact original jump tsum/intrinsic kernel integral equality, set s=0 and use X.X_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Same-space original BV path equals source generator drift minus its entire
actual negative-left-jump sum, globally on one full-measure event. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_laplace_global_path
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
