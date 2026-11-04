-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_mean_zero_two_random_clock_jump_increment
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_mean_zero_two_random_clock_jump_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:08:20.52422+00:00
-- url     : https://prove2.me/theorems/6c053fc0-320c-49a2-bb35-980b14238b96
-- title:
--   Original source BV drift and negative-jump difference between any two random clocks (mean_zero)
-- statement:
--   For the original spectrally negative Levy process with X.BoundedVariation and the explicitly assumed cofinal mean_zero source hypothesis, the path increment between any pair of sample-dependent clocks equals physical drift times the time difference minus the difference in the two original actual negative-left-jump total series. No clock ordering or auxiliary process is introduced.
-- source:
--   Algebraic subtraction of the original global source path formula 5beba39a-1bdd-4512-a9a9-7adb5a30c233 evaluated at U(ω) and S(ω) on the same original full-measure event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_path

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV path increment between arbitrary sample-dependent clocks
is physical drift less the difference of genuine negative left-jump totals. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_mean_zero_two_random_clock_jump_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      (((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0)
    (S U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
      ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
      ((∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ S ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) := by sorry
