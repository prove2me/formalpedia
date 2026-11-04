-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_mean_zero_global_path
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_mean_zero_global_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:20:42.289202+00:00
-- url     : https://prove2.me/theorems/a25a8b36-8500-4742-bbbe-2ab4767d9f51
-- title:
--   Original Lévy BV complete all-time physical drift and negative-left-jump series
-- statement:
--   For the true original BV spectrally negative Levy process, if its residual physical drift less actual jump variation is integrable and mean-zero at each integer horizon, one probability-one event supports for all real nonnegative times the exact original X_t = t X.drift minus the sum of actual negative left-jump magnitudes. Source X_0=0, no Standing, genuine X.X left limits, source P and filtration. The residual mean-zero obligation remains explicit.
-- source:
--   Proved ecc56f30 interval identity at every integer via countable AE intersection and Proved 3d5eead6 intrinsic jump-tsum encoding; instantiate s=0, rewrite X.X_zero and select n≥t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV sample path equals its source drift minus genuine negative
left-jump magnitudes at all times, under explicit integer residual means. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_mean_zero_global_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      ((((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
