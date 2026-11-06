-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:24:55.418673+00:00
-- url     : https://prove2.me/theorems/5d14bcf5-2b2e-4711-af4a-f5e504e195ee
-- title:
--   Automatic original full-negative-cutoff rightCont bounded predictable L² weighted isometry
-- statement:
--   For the actual original X, P, Levy ν and actual physical marked jump count on (s,s+T] for the full separated negative cutoff, each bounded right-continuously predictable coefficient H has a square-integrable compensated marked-count product and exact isometry with rate Tν(B), with no extrinsic weighted-integrability or moment premises.
-- source:
--   Direct original full-cutoff shifted variance supplies integrable count square. The physical bounded H² count square is dominated by L² times integrable source square. Global measurability follows from rightCont strong measurability, yielding MemLp. The exact source isometry uses the Proved prior full-cutoff rightCont weighted conditional isometry.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_weighted_isometry
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P ∧
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by sorry
