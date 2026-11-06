-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_collision_shorttime_L2_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_shorttime_L2_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:13:19.480204+00:00
-- url     : https://prove2.me/theorems/5cbae3b7-011c-4489-a9e7-fad804609bab
-- title:
--   Original bounded negative-band collision squared error vanishes on shrinking horizons
-- statement:
--   For the original physical negative-band count at horizon T/k, measurable uniformly bounded stochastic weights have squared collision error whose expectation tends to zero. Quantitative upper bound: 2 B² (T ν_band / k)² for k>0. This upgrades physical stochastic short-time collision control from L1 to L2 for Itô–Meyer martingale approximation.
-- source:
--   Original accepted weighted collision second moment ce7fd8b7 and exact physical horizon rate c3093fe5; squeeze by quadratic rate.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_shorttime_L2_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : ℕ → Ω → ℝ) (hHm : ∀ k, Measurable (H k))
    (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ k ω, |H k ω| ≤ B) :
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, (H k ω * (if 2 ≤ K k ω then (K k ω : ℝ) else 0)) ^ 2 ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
