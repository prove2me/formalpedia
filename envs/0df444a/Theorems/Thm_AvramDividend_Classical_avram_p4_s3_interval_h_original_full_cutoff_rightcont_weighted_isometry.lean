-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_weighted_isometry
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_weighted_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:17:29.49069+00:00
-- url     : https://prove2.me/theorems/1e4f2e8e-4146-4eb7-b976-c858eed308d6
-- title:
--   Original physical full negative-cutoff right-continuous predictable weighted diagonal L² isometry
-- statement:
--   For the unchanged original Lévy process X and real marked count on the actual shifted physical window (s,s+T] with all negative marks below cutoff, any rightCont-s strongly measurable predictable scalar coefficient H satisfies exact weighted squared L² isometry, assuming only the weighted square is integrable. The single count's conditional second moment is independently source-proved, so no conditional-moment assumption is supplied by the caller. No synthetic marks or finite-band restriction.
-- source:
--   Full-cutoff shifted original second moment and rightCont conditional square; conditional expectation pulls out the rightCont-s measurable scalar H², integrated back to unconditional isometry.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_weighted_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hWeightedSqInt : Integrable
      (fun ω =>
        (H ω)^2 *
          (((((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal) -
            ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)^2) P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by sorry
