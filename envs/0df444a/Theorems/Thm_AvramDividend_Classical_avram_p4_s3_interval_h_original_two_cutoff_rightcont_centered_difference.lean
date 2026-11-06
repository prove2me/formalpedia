-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_two_cutoff_rightcont_centered_difference
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_two_cutoff_rightcont_centered_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:21:39.028258+00:00
-- url     : https://prove2.me/theorems/14e484d2-dfad-449b-aa9d-654be4bed557
-- title:
--   Actual original two-full-cutoff centred-difference L² and same-window rightCont conditional centring
-- statement:
--   For the actual original marked jump count at two nested full negative cutoffs (n and 0) on precisely the same physical window (s,s+T], the difference of their compensated real count functionals is square integrable and its expectation conditional on the original rightCont physical filtration at s vanishes. No independent-copy process, covariance hypothesis or source moment premise.
-- source:
--   Each genuine nested original count is L² from the Proved separated negative Borel count source; each has zero conditional mean by the source exact original cutoff rightCont theorem. L² is closed under subtraction and conditional expectation is linear for integrable operands.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_two_cutoff_rightcont_centered_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
    let C : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    MemLp (fun ω => C n ω - C 0 ω) 2 P ∧
    (P[(fun ω => C n ω - C 0 ω) | 𝓕.rightCont s]
      =ᵐ[P] (fun _ => 0)) := by sorry
