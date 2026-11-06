-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_bounded_predictable_physical_cell_L2_rate
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_bounded_predictable_physical_cell_L2_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:04:47.344119+00:00
-- url     : https://prove2.me/theorems/458fb8a1-0f07-4b56-aa48-ae2c63548e65
-- title:
--   Quantitative exact original full negative-cutoff physical cell L2 upper bound for bounded right-continuous predictable weights
-- statement:
--   For genuine original Levy negative-band jumps on a physical interval (s,s+T], the expected square of a bounded right-continuous predictable coefficient times its compensated jump count is at most L squared multiplied by the original physical Levy intensity Tν(B). No additional conditional second moment hypothesis is required.
-- source:
--   Proved public original full negative-cutoff predictable physical cell exact isometry, probability-measure integral monotonicity and deterministic coefficient bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_bounded_predictable_physical_cell_L2_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r))^2 ∂P) ≤ r * L^2 := by sorry
