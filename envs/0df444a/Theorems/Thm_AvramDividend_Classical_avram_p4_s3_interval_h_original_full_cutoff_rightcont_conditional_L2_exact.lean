-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:54:43.705358+00:00
-- url     : https://prove2.me/theorems/6e3d8547-bbc4-4839-adae-163c2bc4f137
-- title:
--   Original full negative-cutoff compensated marked count has exact conditional mean zero and variance at the true right-continuous filtration
-- statement:
--   For the literal original Lévy marked jump count on any deterministic shifted interval (s,s+T] with physical negative full-cutoff marks, the centred real count has zero conditional expectation and its squared centred count has conditional expectation Tν(B) at the original right-continuous filtration at s. Both results follow from source zero-origin moment facts, proven same-X stationary count law, and source future-path independence. No synthetic process, added future moment hypotheses, stopped optional-sampling claim or law proxy.
-- source:
--   Combines the original full-cutoff L2 integrability 963870c8, exact first mean c1e09ada, newly Proved real source moment stationarity 34cdb144, shifted variance, and existing right-continuous physical conditional moments 4208c6b2. Fully discharges all mean/variance hypotheses for the exact full-cutoff original cell.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => r)) := by sorry
