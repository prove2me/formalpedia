-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_moving_physical_cell_L2_vanishes
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_moving_physical_cell_L2_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:07:16.417544+00:00
-- url     : https://prove2.me/theorems/4bcbe617-5c59-40ce-bb1f-a0cd2c2038a1
-- title:
--   Original negative-cutoff predictable compensated L2 energy vanishes for arbitrarily moving physical time cells of width T/k
-- statement:
--   For every arbitrary moving deterministic start time s(k), a right-continuous predictable coefficient uniformly bounded by L, and the actual original spectrally negative Levy jump count on (s(k),s(k)+T/k], the expected squared compensated cell tends to zero as k grows. The bound is the exact original physical rate L² T ν(B)/k, so the proof uses no source substitution or unverified conditional moments.
-- source:
--   Proved original full-cutoff predictable physical conditional isometry 5d14bcf5 and exact original physical reciprocal-horizon rate c3093fe5, boundedness and real squeeze theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_moving_physical_cell_L2_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (hH : ∀ k, StronglyMeasurable[𝓕.rightCont (s k)] (H k))
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ k ω, |H k ω| ≤ L) :
    let N : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s k) (s k + T / (k : ℝ≥0)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun k =>
      ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, (H k ω * ((N k ω).toReal - r k))^2 ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
